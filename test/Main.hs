{-# LANGUAGE DataKinds, TypeFamilies, TemplateHaskell #-}
module Main(main) where

import Control.HOAG
import Control.Monad.Identity
import Control.MonadFlow
import Data.Proxy
import qualified Data.Type.Dict as D
import Test.QuickCheck
import Test.QuickCheck.Monadic
import Data.Semigroup


idMonadP :: Proxy Identity
idMonadP = Proxy

resumptionMonadP :: Proxy (Resumption t)
resumptionMonadP = Proxy


--
-- The classical repmin example
--

data IntTree = Leaf Int | Node IntTree IntTree

$(genLabels [ "tree", "leaf", "node", "top", "lft", "rght", "gathMin", "distMin", "resTree" ])

prop_testRepmin a b c = monadicIO $ do { x <- run (f a b c); assert $ x == minimum [a, b, c] } where
  m = emptyModule resumptionMonadP
      §§ productions root
         &| root
      §§ productions tree
         &| leaf
         &| node
      §§ attributes root &: tree
         § syn resTree
      §§ attributes tree
         § inh distMin
         § syn gathMin  ::: (Proxy :: Proxy (Min Int))
      §§ rules root root
         § top  ?: tree    := (this >>= mkTree)
         § top  ?  distMin := (getMin <$> top ! gathMin)
      §§ rules tree leaf
         § lhs  ?  gathMin := (Min  <$> this)
         § lhs  ?  resTree := (Leaf <$> lhs ! distMin)
      §§ rules tree node
         § lft  ?: tree    := (this >>= mkTree . fst)
         § rght ?: tree    := (this >>= mkTree . snd)
         § lhs  ?  resTree := (Node <$> lft ! resTree <*> rght ! resTree)

  mkTree (Leaf x)   = prod tree leaf x
  mkTree (Node p q) = prod tree node (p, q)

  prog = weave m

  f a b c = runResumption D.empty
      $ do let inhs = D.empty
               tree = Node (Leaf a) (Node (Leaf b) (Leaf c))
           syns  <- eval prog root root tree inhs
           tree' <- merge (syns D.! resTree)
           case tree' of
             Node (Leaf z) _ -> pure z


--
-- Some miscellaneous tests of various features
--

$(genLabels [ "ntA", "prodA1", "ntB", "prodB1", "ntC", "prodC1", "attrX", "attrY", "attrZ", "attrA", "attrB", "attrC", "childC", "childD" ])

prop_testFeatureMix z = f z === 2 * (z + 1) where
  m = emptyModule idMonadP
      §§ productions ntA &| prodA1
      §§ productions ntB &| prodB1
      §§ attributes ntA &: ntB
         § inh attrX ::: (Proxy :: Proxy Int)
         § syn attrY
      §§ rules ntA prodA1
         § childC ?: ntB   := (prod ntB prodB1 ())
         § childC ?  attrX := 1
         § loc    ?  attrX := (lhs ! attrX)
         § lhs    ?  attrY := (loc ! attrX * childC ! attrY)
      §§ rules ntB prodB1
         § lhs    ?  attrY := (lhs ! attrX + 1)
      §§ rules ntA prodA1
         § loc    ?  attrX :+ (+1)

  p = weave m

  f z = runIdentity $
    do x <- fork $ pure z
       let inhs = D.singleton attrX x
       syns <- eval p ntA prodA1 () inhs
       merge (syns D.! attrY)


prop_testTuplePat (a, b) = f (a, b) === (b, a) where
  m = emptyModule idMonadP
      §§ productions ntA &| prodA1
      §§ attributes ntA
         § inh attrX
         § syn attrY
         § syn attrZ
      §§ rules ntA prodA1
         § attrX @? lhs ? attrZ :*: lhs ? attrY := (lhs ! attrX)

  p = weave m

  f z = runIdentity $
    do x <- fork $ pure z
       let inhs = D.singleton attrX x
       syns <- eval p ntA prodA1 () inhs
       (,) <$> merge (syns D.! attrY) <*> merge (syns D.! attrZ)


prop_testLhsTypeRedef z = f z === (show z) where
  m = emptyModule idMonadP
      §§ productions ntA &| prodA1
      §§ attributes ntA
         § inh attrX ::: (Proxy :: Proxy Int)
         § syn attrY
      §§ rules ntA prodA1
         § lhs ? attrY := lhs ! attrX
      §§ rules ntA prodA1
         § lhs ? attrY :+ fmap show

  p = weave m

  f z = runIdentity $
    do x <- fork $ pure z
       let inhs = D.singleton attrX x
       syns <- eval p ntA prodA1 () inhs
       merge (syns D.! attrY)

prop_testLocTypeRedef z = f z === (show z) where
  m = emptyModule idMonadP
      §§ productions ntA &| prodA1
      §§ attributes ntA
         § inh attrX ::: (Proxy :: Proxy Int)
         § syn attrY
      §§ rules ntA prodA1
         § loc ? attrX := lhs ! attrX
         § lhs ? attrY := loc ! attrX
      §§ rules ntA prodA1
         § loc ? attrX :+ fmap show

  p = weave m

  f z = runIdentity $
    do x <- fork $ pure z
       let inhs = D.singleton attrX x
       syns <- eval p ntA prodA1 () inhs
       merge (syns D.! attrY)


prop_testInhSynAuto z = f z === z + 1 where
  m = emptyModule idMonadP
      §§ productions ntA &| prodA1
      §§ productions ntB &| prodB1
      §§ attributes ntA &: ntB
         § inh attrX ::: (Proxy :: Proxy Int)
         § syn attrY
      §§ rules ntA prodA1
         § childC ?: ntB   := (prod ntB prodB1 ())
      §§ rules ntB prodB1
         § lhs    ?  attrY := (lhs ! attrX + 1)

  p = weave m

  f z = runIdentity $
    do x <- fork $ pure z
       let inhs = D.singleton attrX x
       syns <- eval p ntA prodA1 () inhs
       merge (syns D.! attrY)

prop_testInhSynAutoCombine z = f z === (z + 1) * 2 where
  m = emptyModule idMonadP
      §§ productions ntA &| prodA1
      §§ productions ntB &| prodB1
      §§ attributes ntA &: ntB
         § inh attrX ::: (Proxy :: Proxy (Sum Int))
         § syn attrY
      §§ rules ntA prodA1
         § childC ?: ntB   := (prod ntB prodB1 ())
         § childD ?: ntB   := (prod ntB prodB1 ())
      §§ rules ntB prodB1
         § lhs    ?  attrY := (lhs ! attrX + 1)

  p = weave m

  f z = runIdentity $
    do x <- fork $ pure z
       let inhs = D.singleton attrX x
       syns <- eval p ntA prodA1 () inhs
       merge (syns D.! attrY)


prop_testSeveralLocs z = f z === z where
  m = emptyModule idMonadP
      §§ productions ntA &| prodA1
      §§ attributes ntA
         § inh attrX ::: (Proxy :: Proxy (Sum Int))
         § syn attrX
         § syn attrY
         § syn attrZ
         § syn attrA
         § syn attrB
         § syn attrC
      §§ rules ntA prodA1
         § loc ? attrX := lhs ! attrX
      §§ rules ntA prodA1
         § loc ? attrY := lhs ! attrX
      §§ rules ntA prodA1
         § loc ? attrZ := lhs ! attrX
      §§ rules ntA prodA1
         § loc ? attrA := lhs ! attrX
      §§ rules ntA prodA1
         § loc ? attrB := lhs ! attrX
      §§ rules ntA prodA1
         § loc ? attrC := lhs ! attrX

  p = weave m

  f z = runIdentity $
    do x <- fork $ pure z
       let inhs = D.singleton attrX x
       syns <- eval p ntA prodA1 () inhs
       merge (syns D.! attrX)


prop_testList z = f z === 3 * (z + 1) where
  m = emptyModule idMonadP
      §§ productions ntA &| prodA1
      §§ productions ntB &| prodB1
      §§ declList ntB ntC (prod ntB prodB1)

      §§ attributes ntA &: ntB &: ntC
         § inh attrX ::: (Proxy :: Proxy (Sum Int))
         § syn attrX

      §§ rules ntA prodA1
         § childC ?: ntC := mkList ntC [(),(),()]

      §§ rules ntB prodB1
         § loc ? attrX := lhs ! attrX + 1

  p = weave m

  f z = runIdentity $
    do x <- fork $ pure z
       let inhs = D.singleton attrX x
       syns <- eval p ntA prodA1 () inhs
       merge (syns D.! attrX)


prop_testSink x y = f x y === x + y where
  m = emptyModule idMonadP
      §§ declSink ntA
      §§ attributes ntA
         § inh attrX ::: (Proxy :: Proxy Int)
         § inh attrY ::: (Proxy :: Proxy Int)

  p = weave m

  f a b = runIdentity $
    do x <- fork $ pure (a :: Int)
       y <- fork $ pure (b :: Int)
       let inhs = D.insert attrX x $ D.insert attrY y $ D.empty
       syns <- eval p ntA nil () inhs
       r <- merge (syns D.! val)
       x' <- merge (r D.! attrX)
       y' <- merge (r D.! attrY)
       pure (x' + y')


prop_testAround x = f x === x where
  m = emptyModule idMonadP
      §§ productions ntA &| prodA1
      §§ attributes ntA
         § inh attrX
         § syn attrY
      §§ rules ntA prodA1
         § childC ?: ntA := (aroundChild (const g) (prod ntA prodA1 ()))

  g inh = pure $ D.singleton attrY (inh D.! attrX)

  p = weave m

  f z = runIdentity $
   do x <- fork $ pure z
      let inhs = D.singleton attrX x
      syns <- eval p ntA prodA1 () inhs
      merge (syns D.! attrY)

prop_testMergeDict x
  = monadicIO $ do
      z <- run (f x)
      assert (2 * x + 1 == z)
  where
    f z = runResumption D.empty $
      do x <- fork $ pure z
         y <- fork $ pure z
         c <- fork $ pure 1
         let r = D.insert attrC c $ D.insert attrY y $ D.singleton attrX x
         r' <- mergeDict r
         pure (r' D.! attrX + r' D.! attrY + r' D.! attrC)


--
-- Runs the tests defined in this unit.
--

return []
main = $quickCheckAll
