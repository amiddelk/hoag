{-# LANGUAGE TypeFamilies, GADTs, ExistentialQuantification, GeneralizedNewtypeDeriving, FlexibleInstances #-}
{-# LANGUAGE ConstraintKinds, DataKinds, TypeOperators, MultiParamTypeClasses, UndecidableInstances #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE Trustworthy #-}
module Control.MonadFlow
  ( MonadFlow(..)
  , Fiber, runFiber
  , Resumption, PendingAction(..), ActionProcessor(..), ActionProcs, runResumption, action, action1, restrictAction, ioAction, mkIOProcessor, ActionIO, actionIO, actionIO_
  , MergeVars, MergeDict(..)
  ) where

import Control.Applicative
import Control.Concurrent
import Control.Exception hiding (TypeError)
import Control.Monad
import Control.Monad.Except
import Control.Monad.Fail hiding(fail)
import qualified Control.Monad.Fail as F
import Control.Monad.IO.Class
import Control.Monad.Zip
import Data.HashMap.Strict(HashMap)
import qualified Data.HashMap.Strict as HM
import Data.Kind(Type, Constraint)
import Data.Sequence(Seq)
import qualified Data.Sequence as Seq
import Control.Monad
import Control.Monad.Identity
import Control.Monad.Reader
import Data.IntMap(IntMap)
import qualified Data.IntMap.Strict as IM
import Data.IORef
import Data.Proxy
import qualified Data.Text as T
import qualified Data.Type.Dict as D
import GHC.IO.Exception
import GHC.Exts
import GHC.TypeLits
import Unsafe.Coerce


--
-- Monad for constructing dataflow graphs.
--

class Monad m => MonadFlow m where
  type Branch m :: Type -> Type
  fork  :: m a         -> m (Branch m a)
  merge :: Branch m a  -> m a
  loop  :: (Branch m b -> m (a, Branch m b)) -> m a


--
-- (demand-driven) Instance for the identity monad
--

data Lazy a = Lazy ~a

instance MonadFlow Identity where
  type Branch Identity = Lazy
  fork  (Identity x) = Identity $ Lazy x
  merge (Lazy x)     = pure x
  loop f
    = let Identity ~(a, Lazy b) = f (Lazy b)
      in Identity a


--
-- (demand-driven) Instance for the IO monad
--

data Thunk a
  = ThunkVal a
  | ThunkErr SomeException
  | ThunkComp (IO a)

newtype ThunkRef a = ThunkRef (IORef (Thunk a))

instance MonadFlow IO where
  type Branch IO = ThunkRef
  fork m = ThunkRef <$> (newIORef $ ThunkComp m)
  merge (ThunkRef r)
    = do t <- readIORef r
         case t of
           ThunkVal a  -> pure a
           ThunkErr e  -> throwIO e
           ThunkComp m -> do
             writeIORef r $ ThunkErr $ toException Deadlock
             z <- run m
             case z of
               Left e -> do
                 writeIORef r $ ThunkErr e
                 throwIO e
               Right v -> do
                 writeIORef r $ ThunkVal v
                 pure v
    where
      run m = consumeExceptions Left Right m
  loop f
    = do r <- newIORef $ ThunkErr $ toException Deadlock
         (a, ThunkRef r') <- f (ThunkRef r)
         t <- readIORef r'
         writeIORef r t
         pure a


--
-- Fiber: guarantees execution of each rule
--

newtype Fiber a = Fiber (ReaderT Env IO a)
  deriving (Functor, Applicative, Alternative, Monad)

data Env = Env (IORef (IntMap SomeThunkRef)) (IORef Int)
data SomeThunkRef = forall a . SomeThunkRef (ThunkRef a)

instance MonadFlow Fiber where
  type Branch Fiber = ThunkRef
  fork (Fiber m) = Fiber $ do
    env@(Env mpRef cntRef) <- ask
    lift $ do
      cnt <- readIORef cntRef
      writeIORef cntRef $! cnt + 1
      t <- fork $ do
        modifyIORef' mpRef (IM.delete cnt)
        runReaderT m env
      modifyIORef' mpRef $ IM.insert cnt (SomeThunkRef t)
      pure t
  merge = Fiber . lift . merge
  loop f = Fiber $ do
    env@(Env _ cntRef) <- ask
    lift $ do
      loop $ \r ->
           case f r of
             Fiber m -> runReaderT m env

runFiber :: Fiber a -> IO a
runFiber (Fiber m) = do
  mpRef  <- newIORef IM.empty
  cntRef <- newIORef 1
  let env = Env mpRef cntRef
  a <- runReaderT m env
  fiberLoop env
  pure a

fiberLoop :: Env -> IO ()
fiberLoop env@(Env mpRef cntRef) = loop where
  loop = do
    mp <- readIORef mpRef
    case IM.minView mp of
      Just (SomeThunkRef r, mp') -> do
        writeIORef mpRef mp'
        merge r
        loop
      Nothing -> return ()


--
-- Resumption monad - resumeable computations with explicit effects that can be batched
--

data PendingAction req = forall s a . PendingAction (req s a) (Either SomeException a -> IO ())

data ActionProcessor req = ActionProcessor
  { startPendingActions  :: IO ()
  , finishPendingActions :: IO ()
  , abortPendingActions  :: SomeException -> IO ()
  , addPendingAction     :: PendingAction req -> IO ()
  }

type ActionProcs t = D.Rec t

newtype Resumption t a = Resumption { unResumption :: Ctx t -> IO (Result t a) }

data Ctx t = Ctx { ctxCurrentNode :: Node t, ctxNodes :: IORef (Nodes t), ctxActions :: ActionProcs t }

data Node t = forall a . Node (IORef (Resumption t a)) (Var t a)
type Nodes t = Seq (Node t)

data Val a
  = ValUndefined
  | ValDefined a
  | ValExcept SomeException

data Var t a = Var (IORef (Val a)) (IORef (Nodes t))

data Result t a
  = Done a
  | Throw SomeException
  | Blocked (Cont t a)

data Cont t a
  = Cont (Resumption t a)
  | forall b . Cont t b :>>= (b -> Resumption t a)
  | forall b . (Cont t (b -> a)) :<*> (Cont t b)
  | forall b . (b -> a) :<$> (Cont t b)

toResumption :: Cont t a -> Resumption t a
toResumption (Cont m)              = m
toResumption ((m :>>= f) :>>= g)   = toResumption $ m :>>= (f >=> g)
toResumption (c :>>= k)            = toResumption c >>= k
toResumption ((f :<$> i) :<*> (g :<$> j))
  = toResumption $ ((\x y -> f x (g y)) :<$> i) :<*> j
toResumption (f :<*> x)            = toResumption f <*> toResumption x
toResumption (f :<$> (g :<$> x))   = toResumption $ (f . g) :<$> x
toResumption (f :<$> x)            = fmap f $ toResumption x

instance Monad (Resumption t) where
  return a = Resumption $ \_ -> return $ Done a
  Resumption m >>= k = Resumption $ \ctx -> do
    e <- m ctx
    case e of
      Done a       -> unResumption (k a) ctx
      Throw e      -> return $ Throw e
      Blocked cont -> return $ Blocked $ cont :>>= k
  fail msg = Resumption $ \_ -> return $ Throw $ toException $ ErrorCall msg
  (>>) = (*>)

instance Functor (Resumption t) where
  fmap f (Resumption m) = Resumption $ \ctx -> do
    r <- m ctx
    case r of
      Done a     -> return $ Done $ f a
      Throw e    -> return $ Throw e
      Blocked a' -> return $ Blocked $ f :<$> a'

instance Applicative (Resumption t) where
  pure = return
  Resumption f <*> Resumption a = Resumption $ \ctx -> do
    r <- f ctx
    case r of
      Throw e -> return $ Throw e
      Done f' -> do
        ra <- a ctx
        case ra of
          Done a'    -> return $ Done $ f' a'
          Throw e    -> return $ Throw e
          Blocked a' -> return $ Blocked $ f' :<$> a'
      Blocked f' -> do
        ra <- a ctx
        case ra of
          Done a'    -> return $ Blocked $ ($ a') :<$> f'
          Throw e    -> return $ Blocked $ f' :<*> Cont (throw e)
          Blocked a' -> return $ Blocked $ f' :<*> a'

data Incomplete = Incomplete

instance Show Incomplete where
  show _ = "Incomplete"

instance Exception Incomplete

instance Alternative (Resumption t) where
  empty   = throwError $ toException Incomplete
  f <|> g = do
    v <- fork f
    ea <- merge0 v
    case ea of
      Right a -> pure a
      Left e  -> case fromException e of
        Just Incomplete -> g
        Nothing         -> throwError e

instance MonadFlow (Resumption t) where
  type Branch (Resumption t) = Var t

  fork m = Resumption $ \ctx -> do
    v <- newEmptyVar
    mref <- newIORef m
    let nd = Node mref v
        nsRef = ctxNodes ctx
    modifyIORef' nsRef (nd Seq.<|)
    return $ Done v

  merge var@(Var vref fref) = Resumption $ \ctx -> do
    v <- readIORef vref
    case v of
      ValUndefined -> do
        let merge' = Resumption $ \ctx -> do
              v' <- readIORef vref
              case v' of
                ValUndefined -> return $ Blocked $ Cont merge'
                ValDefined v -> return $ Done v
                ValExcept e  -> return $ Throw e
        modifyIORef' fref (ctxCurrentNode ctx Seq.<|)
        return $ Blocked $ Cont merge'
      ValDefined v -> return $ Done v
      ValExcept e  -> return $ Throw e

  loop f = Resumption $ \ctx -> do
    v  <- newEmptyVar
    v'@(Var vref fref) <- newEmptyVar
    mref  <- newIORef (f v)
    mref1 <- newIORef (snd <$> merge v' >>= merge)
    let nd    = Node mref v'
        nsRef = ctxNodes ctx
        nd1   = Node mref1 v
        nd2   = ctxCurrentNode ctx
    modifyIORef' nsRef (\fs -> nd Seq.<| nd1 Seq.<| nd2 Seq.<| fs)
    let merge' = Resumption $ \ctx -> do
          v' <- readIORef vref
          case v' of
            ValUndefined -> return $ Blocked $ Cont merge'
            ValDefined v -> return $ Done $ fst v
            ValExcept e  -> return $ Throw e
    modifyIORef' fref (ctxCurrentNode ctx Seq.<|)
    return $ Blocked $ Cont merge'

merge0 :: Var t a -> Resumption t (Either SomeException a)
merge0 var@(Var vref fref) = Resumption $ \ctx -> do
  v <- readIORef vref
  case v of
   ValUndefined -> do
     let merge' = Resumption $ \ctx -> do
           v' <- readIORef vref
           case v' of
             ValUndefined -> return $ Blocked $ Cont merge'
             ValDefined v -> return $ Done $ Right v
             ValExcept e  -> return $ Done $ Left e
     modifyIORef' fref (ctxCurrentNode ctx Seq.<|)
     return $ Blocked $ Cont merge'
   ValDefined v -> return $ Done $ Right v
   ValExcept e  -> return $ Done $ Left e

action :: (KnownSymbol k, t D.:! k ~ ActionProcessor req) => Proxy k -> req s a -> Resumption t (Var t a)
action k req = Resumption $ \ctx ->
  let env = ctxActions ctx D.! k
  in do v@(Var vref fref) <- newEmptyVar
        addPendingAction env $ PendingAction req $ \ea -> do
          writeIORef vref $! case ea of
            Left err -> ValExcept err
            Right v  -> ValDefined v
          fs <- readIORef fref
          modifyIORef' (ctxNodes ctx) (fs Seq.><)
          writeIORef fref Seq.empty
        pure $ Done v

action1 :: (KnownSymbol k, t D.:! k ~ ActionProcessor req) => Proxy k -> req s a -> Resumption t a
action1 p r = action p r >>= merge

runResumption :: ActionProcs t -> Resumption t a -> IO a
runResumption acts m
  = do rvar <- newEmptyVar
       mref <- newIORef m
       let nd = Node mref rvar
       nodes <- newIORef $! Seq.singleton nd
       execNodes acts nodes
       case rvar of
         Var r _ -> do
           v <- readIORef r
           case v of
             ValUndefined -> throwIO $ toException $ Deadlock
             ValDefined a -> return a
             ValExcept e  -> throwIO $ toException e

execNodes :: ActionProcs t -> IORef (Nodes t) -> IO ()
execNodes acts nsRef = outerloop where
  outerloop = do
    innerloop
    runActions acts
    nodes <- readIORef nsRef
    if Seq.null nodes
     then return ()
     else outerloop

  innerloop = do
    nodes <- readIORef nsRef
    case Seq.viewl nodes of
      Seq.EmptyL -> return ()
      (nd Seq.:< ns) -> do
        writeIORef nsRef ns
        execNode acts nd nsRef
        innerloop

runActions :: ActionProcs t -> IO ()
runActions acts
  = do mapM_ (coerceProc startPendingActions) procs
       mapM_ (coerceProc finishPendingActions) procs `catch` signalException
  where
    procs = HM.elems $ D.assocs acts
    signalException e = mapM_ (coerceProc' abortPendingActions e) procs >> throwIO e

    coerceProc :: (ActionProcessor t -> IO ()) -> Any -> IO ()
    coerceProc = unsafeCoerce
    
    coerceProc' :: (ActionProcessor t -> SomeException -> IO ()) -> SomeException -> Any -> IO ()
    coerceProc' = unsafeCoerce

untouchableResumption :: Resumption t a
untouchableResumption = Resumption $ \_ -> fail "Internal error"

execNode :: ActionProcs t -> Node t -> IORef (Nodes t) -> IO ()
execNode acts nd@(Node mref (Var rref fref)) nsRef = do
  val <- readIORef rref
  case val of
    ValUndefined -> do
      writeIORef rref $ ValExcept $ toException $ Deadlock
      m <- readIORef mref
      let ctx' = Ctx nd nsRef acts
      res <- consumeExceptions Throw id $ reduce m ctx'
      case res of
        Blocked _ -> do
          writeIORef rref ValUndefined
          writeIORef mref $ Resumption $ \_ -> return res
        _         -> do
          writeIORef mref untouchableResumption
          case res of
            Done v  -> writeIORef rref $ ValDefined v
            Throw e -> writeIORef rref $ ValExcept e
          fs <- readIORef fref
          modifyIORef' nsRef (fs Seq.><)
          writeIORef fref Seq.empty
    _ -> return ()

consumeExceptions :: (SomeException -> b) -> (a -> b) -> IO a -> IO b
consumeExceptions f g m = (g <$> m) `catches` handlers where
  handlers = [ Handler $ \e -> pure $ f $ toException (e :: Incomplete)
             , Handler $ \e -> pure $ f $ toException (e :: ArithException)
             , Handler $ \e -> pure $ f $ toException (e :: ErrorCall)
             , Handler $ \e -> pure $ f $ toException (e :: PatternMatchFail )
             , Handler $ \e ->
                 case ioe_type e of
                   UserError -> pure $ f $ toException e
                   _         -> throwIO e
             ]

reduce :: Resumption t a -> Ctx t -> IO (Result t a)
reduce (Resumption m) ctx = do
  res <- m ctx
  case res of
    Blocked cont -> reduce' (toResumption cont) ctx
    _            -> return res

reduce' :: Resumption t a -> Ctx t -> IO (Result t a)
reduce' (Resumption m) ctx = m ctx

newEmptyVar :: IO (Var t a)
newEmptyVar = do
  valRef  <- newIORef ValUndefined
  succRef <- newIORef Seq.empty
  return $ Var valRef succRef

newtype ActionIO s a = PerformIO (IO a)

mkIOProcessor :: IO (ActionProcessor ActionIO)
mkIOProcessor
  = do pendingRef <- newIORef Seq.empty
       pure $ ActionProcessor
         { startPendingActions  = return ()
         , finishPendingActions = do
             pending <- readIORef pendingRef
             mapM_ runPending pending
             writeIORef pendingRef Seq.empty
         , abortPendingActions = \e -> do
             pending <- readIORef pendingRef
             writeIORef pendingRef Seq.empty
             mapM_ (abortPending e) pending
         , addPendingAction = \p -> modifyIORef' pendingRef (Seq.|> p)
         }
  where
    runPending (PendingAction (PerformIO m) f) = consumeExceptions Left Right m >>= f
    abortPending e (PendingAction _ f) = f (Left e)

ioAction :: Proxy "IO"
ioAction = Proxy

actionIO :: t D.:! "IO" ~ ActionProcessor ActionIO => IO a -> Resumption t a
actionIO m = action1 ioAction (PerformIO m)

actionIO_ :: t D.:! "IO" ~ ActionProcessor ActionIO => IO () -> Resumption t ()
actionIO_ m = void $ action ioAction (PerformIO m)

restrictAction :: KnownSymbol k => Proxy k -> Resumption (D.Delete k t) a -> Resumption t a
restrictAction _ m = unsafeCoerce m

type HasIOAction t = HasIOAction' (D.Member "IO" t)
type family HasIOAction' r :: Constraint where
  HasIOAction' 'True  = ()
  HasIOAction' 'False = TypeError ('Text "IO actions undeclared")

-- Note: this implementation does not queue the IO actions in order to provide an
-- efficient trap door for IO effects. Use actionIO or actionIO_ to batch IO actions.
instance HasIOAction t => MonadIO (Resumption t) where
  liftIO m = Resumption $ \_ -> consumeExceptions Throw Done m

instance MonadZip (Resumption t) where
  mzipWith f p q = f <$> p <*> q

instance MonadPlus (Resumption t) where
  mzero = empty
  mplus = (<|>)

instance MonadFail (Resumption t) where
  fail = Control.Monad.fail

instance MonadError SomeException (Resumption t) where
  throwError e = Resumption $ \_ -> pure $ Throw e
  catchError m h = do
    v <- fork m
    ea <- merge0 v
    case ea of
      Left e  -> h e
      Right a -> pure a


--
-- Merge a dictionary
--

type family MergeVars ps t where
  MergeVars ps ('D.Bin n s (Var ps a) l r) = 'D.Bin n s a (MergeVars ps l) (MergeVars ps r)
  MergeVars _  'D.Tip                      = 'D.Tip

class MergeDict (t :: D.Dict Type) ps where
  mergeDict :: D.Rec t -> Resumption ps (D.Rec (MergeVars ps t))

instance MergeDict 'D.Tip ps where
  mergeDict _ = pure (D.Rec HM.empty)

instance (KnownSymbol s, MergeDict l ps, MergeDict r ps) => MergeDict ('D.Bin n s (Var ps a) l r) ps where
  mergeDict d@(D.Rec m)
    = do (D.Rec l') <- mergeDict (l d)
         (D.Rec r') <- mergeDict (r d)
         let v = toV d $ HM.lookupDefault (error "Internal error") s m
         v' <- toAny <$> merge v
         pure $ D.Rec $ HM.insert s v' (HM.union l' r')
    where    
      toV :: D.Rec ('D.Bin n s (Var ps a) l r) -> Any -> (Var ps a)
      toV _ x = unsafeCoerce x
      
      toAny :: t -> Any
      toAny x = unsafeCoerce x

      s = T.pack $ symbolVal $ k d
      
      k :: D.Rec ('D.Bin n s (Var ps a) l r) -> Proxy s
      k _ = Proxy

      l :: D.Rec ('D.Bin n s (Var ps a) l r) -> D.Rec l
      l (D.Rec m) = D.Rec m
      
      r :: D.Rec ('D.Bin n s (Var ps a) l r) -> D.Rec r
      r (D.Rec m) = D.Rec m
