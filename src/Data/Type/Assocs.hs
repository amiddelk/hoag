{-# LANGUAGE TypeFamilies, TypeOperators, DataKinds, PolyKinds, UndecidableInstances, TypeInType #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts, BangPatterns, ConstraintKinds #-}
{-# LANGUAGE Trustworthy #-}
module Data.Type.Assocs
  ( Dict(..)
  , Empty, Singleton, Null, Size, Lookup, Find, type (:!), type (:!?), Member, Insert, Assocs, Keys, FromList
  , Rec, empty, singleton, insert, find, (!), (!?), assocs, unsafeFromAssocs, keys, MaybeEqual
  , IsMember, IsAbsent
  , Normalize, normalize
  , ToKeylist, keylist, keyset
  , EnumVal(..), mkEnum, parseEnum, MkEnumMap, MkEnumRevMap, enumSym
  , generateKeyLabels, generateNewKeyLabels
  ) where

import Data.HashMap.Strict(HashMap)
import qualified Data.HashMap.Strict as HM
import Data.IntMap.Strict(IntMap)
import qualified Data.IntMap.Strict as IM
import Data.Kind (Type, Constraint)
import Data.List(sort)
import Data.Proxy
import Data.Set(Set)
import qualified Data.Set as S
import Data.Text(Text)
import qualified Data.Text as T
import GHC.Exts
import GHC.TypeLits
import Language.Haskell.TH hiding (Type)
import Unsafe.Coerce


--
-- Typelevel version of an association list with Symbols as keys
--

type Dict a = [(Symbol, a)]

type Singleton k v = '[ '(k, v) ]

type Empty = '[]

type family Null t where
  Null '[] = 'True
  Null _   = 'False

type family Size t where
  Size '[] = 0
  Size (_ ': xs) = 1 + Size xs

type family Lookup k t where
  Lookup _ '[]              = 'Nothing
  Lookup k ( '(k, v) ': _)  = 'Just v
  Lookup k ( _       ': xs) = Lookup k xs

type family Find k t where
  Find k '[]              = TypeError ('Text "Element not in assoc-list: " :<>: ShowType k)
  Find k ( '(k, v) ': _)  = v
  Find k ( _       ': xs) = Find k xs

type t :!? k = Lookup k t

infixl 9 :!?

type t :! k  = Find k t

infixl 9 :!

type family Member k t where
  Member _ '[]              = 'False
  Member k ( '(k, v) ': _)  = 'True
  Member k ( _       ': xs) = Member k xs

type IsMember k t = IsMember' (Member k t) k
type family IsMember' b k :: Constraint where
  IsMember' 'True  _ = ()
  IsMember' 'False k = TypeError ('Text "Key is not present in map: " :<>: ShowType k)

type IsAbsent k t = IsAbsent' (Member k t) k
type family IsAbsent' b k :: Constraint where
  IsAbsent' 'False _ = ()
  IsAbsent' 'True  k = TypeError ('Text "Key is present in map: " :<>: ShowType k)

type family Insert k v t where
  Insert k v '[]                = '[ '(k, v) ]
  Insert k v ('( k', v') ': xs) = Insert' (CmpSymbol k k') k k' v v' xs

type family Insert' cmp k k' v v' xs where
  Insert' 'EQ k _  v _  xs = '( k, v) ': xs
  Insert' 'LT k k' v v' xs = '( k, v) ': '( k', v') ': xs
  Insert' 'GT k k' v v' xs = '( k', v') : Insert k v xs


type Assocs    (t :: Dict a) = t
type FromList  (t :: Dict a) = t
type Normalize (t :: Dict a) = t

type family Keys t where
  Keys '[]              = '[]
  Keys ( '(k, _) ': xs)  = k ': Keys xs


--
-- Get the type level keys
--
  
class ToKeylist (t :: [Symbol]) where
  toKeylist :: Proxy t -> [Text]

instance ToKeylist '[] where
  toKeylist _ = []

instance (KnownSymbol x, ToKeylist xs) => ToKeylist (x ': xs) where
  toKeylist p = (T.pack $ symbolVal $ hd p) : toKeylist (tl p) where
    hd :: Proxy (x ': xs) -> Proxy x
    hd _ = Proxy
    tl :: Proxy (x ': xs) -> Proxy xs
    tl _ = Proxy

keylist :: ToKeylist (Keys t) => Proxy t -> [Text]
keylist p = toKeylist (trf p) where
  trf :: Proxy t -> Proxy (Keys t)
  trf _ = Proxy

keyset :: ToKeylist (Keys t) => Proxy t -> Set Text
keyset = S.fromList . keylist


--
-- Record described by the dictionary
--

newtype Rec t = Rec (HashMap Text Any)

empty :: Rec Empty
empty = Rec HM.empty

singleton :: KnownSymbol k => Proxy k -> v -> Rec (Singleton k v)
singleton k v = Rec $ HM.singleton (T.pack $ symbolVal k) (unsafeCoerce v)

insert :: KnownSymbol k => Proxy k -> v -> Rec t -> Rec (Insert k v t)
insert k v (Rec m) = Rec $ HM.insert (T.pack $ symbolVal k) (unsafeCoerce v) m

find :: KnownSymbol k => Proxy k -> Rec t -> t :! k
find k (Rec m) = unsafeCoerce (m HM.! (T.pack $ symbolVal k))

(!) :: KnownSymbol k => Rec t -> Proxy k -> t :! k
(!) t k = find k t

infixl 9 !

type family MaybeEqual mb a :: Constraint where
  MaybeEqual ('Just a') a = (a ~ a')
  MaybeEqual 'Nothing   _ = ()

(!?) :: (KnownSymbol k, MaybeEqual (t :!? k) a) => Rec t -> Proxy k -> Maybe a
(Rec m) !? k = unsafeCoerce (HM.lookup (T.pack $ symbolVal k) m)

infixl 9 !?

keys :: Rec t -> [Text]
keys (Rec m) = sort $ HM.keys m

assocs :: Rec t -> HashMap Text Any
assocs (Rec m) = m

unsafeFromAssocs :: HashMap Text a -> Rec t
unsafeFromAssocs m = Rec (unsafeCoerce m)

normalize :: Rec t -> Rec (Normalize t)
normalize (Rec m) = Rec m


--
-- Enumeration described by a Dict Nat where Nat specifies some relative order
--

data EnumVal (t :: Dict Nat) = EnumVal !Text !Int

instance Eq (EnumVal t) where
  (EnumVal s p) == (EnumVal t q) = (p == q) && (s == t)

instance Ord (EnumVal t) where
  compare (EnumVal s p) (EnumVal t q) = compare s t `mappend` compare p q

instance Show (EnumVal t) where
  show (EnumVal s v) = T.unpack $ s `T.snoc` '(' `T.append` (T.pack $ show v) `T.snoc` ')'

instance MkEnumRevMap (Assocs t) => Enum (EnumVal t) where
  toEnum = toEnum' Proxy
  fromEnum (EnumVal _ x) = x

toEnum' :: MkEnumRevMap (Assocs t) => Proxy t -> Int -> EnumVal t
toEnum' p x
  = case IM.lookup x mp of
      Nothing  -> error "EnumVal.toEnum: bad argument"
      Just txt -> EnumVal txt x
  where
    mp = mkEnumRevMap (toAssocsP p)

instance MkEnumRevMap (Assocs t) => Bounded (EnumVal t) where
  minBound = minBound' Proxy
  maxBound = maxBound' Proxy

minBound' :: MkEnumRevMap (Assocs t) => Proxy t -> EnumVal t
minBound' p
  = case IM.findMin $ mkEnumRevMap $ toAssocsP p of
      (v, k) -> EnumVal k v

maxBound' :: MkEnumRevMap (Assocs t) => Proxy t -> EnumVal t
maxBound' p
  = case IM.findMax $ mkEnumRevMap $ toAssocsP p of
      (v, k) -> EnumVal k v

class MkEnumMap (t :: [(Symbol, Nat)]) where
  mkEnumMap :: Proxy t -> HashMap Text Int

instance MkEnumMap '[] where
  mkEnumMap _ = HM.empty

instance (KnownSymbol k, KnownNat v, MkEnumMap xs) => MkEnumMap ('(k, v) ': xs) where
  mkEnumMap p = HM.insert (T.pack $ symbolVal $ k p) (fromInteger $ natVal $ v p) (mkEnumMap $ tl p) where
    tl :: Proxy ('(k, v) ': xs) -> Proxy xs
    tl _ = Proxy

    k :: Proxy ('(k, v) ': xs) -> Proxy k
    k _ = Proxy

    v :: Proxy ('(k, v) ': xs) -> Proxy v
    v _ = Proxy

class MkEnumRevMap (t :: [(Symbol, Nat)]) where
  mkEnumRevMap :: Proxy t -> IntMap Text

instance MkEnumRevMap '[] where
  mkEnumRevMap _ = IM.empty

instance (KnownSymbol k, KnownNat v, MkEnumRevMap xs) => MkEnumRevMap ('(k, v) ': xs) where
  mkEnumRevMap p = IM.insert (fromInteger $ natVal $ v p) (T.pack $ symbolVal $ k p) (mkEnumRevMap $ tl p) where
    tl :: Proxy ('(k, v) ': xs) -> Proxy xs
    tl _ = Proxy

    k :: Proxy ('(k, v) ': xs) -> Proxy k
    k _ = Proxy

    v :: Proxy ('(k, v) ': xs) -> Proxy v
    v _ = Proxy

parseEnum :: MkEnumMap (Assocs t) => Proxy t -> Text -> Maybe (EnumVal t)
parseEnum p txt = EnumVal txt <$> HM.lookup txt mp where
  mp = mkEnumMap $ toAssocsP p

toAssocsP :: Proxy t -> Proxy (Assocs t)
toAssocsP _ = Proxy

mkEnum :: (Find k t ~ v, KnownSymbol k, KnownNat v) => Proxy t -> Proxy k -> EnumVal t
mkEnum t k
  = EnumVal (T.pack $ symbolVal k) (fromInteger $ natVal $ numP k t)
  where
    numP :: Proxy k -> Proxy t -> Proxy (Find k t)
    numP _ _ = Proxy

enumSym :: EnumVal t -> Text
enumSym (EnumVal s _) = s


--
-- Generate labels for typelevel keys
--

genLabel :: Text -> Text -> Q [Dec]
genLabel pre t
  | T.null t  = pure []
  | otherwise = sequence
      [ sigD (mkName s) (appT (conT $ mkName "Proxy") (litT $ strTyLit s))
      , valD (varP $ mkName s) (normalB $ conE $ mkName "Proxy") []
      ]
      where s = T.unpack $ T.append pre t

generateKeyLabels :: ToKeylist (Keys t) => Text -> Proxy t -> Q [Dec]
generateKeyLabels pre p = concat <$> mapM (genLabel pre) (keylist p) where

generateNewKeyLabels :: (ToKeylist (Keys s), ToKeylist (Keys t)) => Text -> Proxy s -> Proxy t -> Q [Dec]
generateNewKeyLabels pre s t = concat <$> (mapM (genLabel pre) $ S.toList $ S.difference (keyset s) (keyset t))
