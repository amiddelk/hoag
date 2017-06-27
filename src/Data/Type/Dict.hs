{-# LANGUAGE TypeOperators, DataKinds, PolyKinds, KindSignatures, TypeFamilies, UndecidableInstances, ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts, BangPatterns #-}
{-# LANGUAGE Trustworthy #-}
module Data.Type.Dict
  ( Dict(..), MinView(..), MaxView(..)
  , Empty, Singleton, Null, Size, Lookup, Find, type (:!), type (:!?), Member, Insert, Delete, Split, Union, Assocs, Keys, FromList
  , IsMember, IsAbsent
  , Rec(..), empty, singleton, insert, find, (!), (!?), delete, union, assocs, unsafeFromAssocs, keys, MaybeEqual
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
-- Typelevel version of Data.Map with Symbols as keys
--

data Dict a =
    Bin Nat Symbol a (Dict a) (Dict a)
  | Tip

data MinView a = MinView Symbol a (Dict a)
data MaxView a = MaxView Symbol a (Dict a)

type Ratio = 2
type Delta = 2

type Empty = 'Tip
type Singleton k x = 'Bin 1 k x 'Tip 'Tip

type family Null t where
  Null 'Tip             = 'True
  Null ('Bin _ _ _ _ _) = 'False

type family Size t where
  Size 'Tip              = 0
  Size ('Bin sz _ _ _ _) = sz

type family Lookup' cmp k x l r where
  Lookup' 'LT k _ l _ = Lookup k l
  Lookup' 'GT k _ _ r = Lookup k r
  Lookup' 'EQ _ x _ _ = 'Just x

type family Lookup k t where
  Lookup k ('Bin _ kx x l r) = Lookup' (CmpSymbol k kx) k x l r
  Lookup _ 'Tip = 'Nothing

type t :!? k = Lookup k t

infixl 9 :!?

type family Find' cmp k x l r where
  Find' 'LT k _ l _ = Find k l
  Find' 'GT k _ _ r = Find k r
  Find' 'EQ _ x _ _ = x

type family Find k t where
  Find k ('Bin _ kx x l r) = Find' (CmpSymbol k kx) k x l r
  Find k 'Tip              = TypeError ('Text "Key not in map: " :<>: ShowType k)

type t :! k  = Find k t

infixl 9 :!

type family Member' cmp k l r where
  Member' 'LT k l _ = Member k l
  Member' 'GT k _ r = Member k r
  Member' 'EQ k _ _ = 'True

type family Member k t where
  Member k ('Bin _ kx _ l r) = Member' (CmpSymbol k kx) k l r
  Member k 'Tip = 'False

type IsMember k t = IsMember' (Member k t) k
type family IsMember' b k :: Constraint where
  IsMember' 'True  _ = ()
  IsMember' 'False k = TypeError ('Text "Key is not present in map: " :<>: ShowType k)

type IsAbsent k t = IsAbsent' (Member k t) k
type family IsAbsent' b k :: Constraint where
  IsAbsent' 'False _ = ()
  IsAbsent' 'True  k = TypeError ('Text "Key is present in map: " :<>: ShowType k)

type family BalanceL_Tip' cmp k x ls lk lx lls llk llx lll llr lrs lrk lrx lrl lrr where
  BalanceL_Tip' 'LT k x ls lk lx lls llk llx lll llr lrs lrk lrx lrl lrr =
    'Bin (1+ls) lk lx ('Bin lls llk llx lll llr) ('Bin (1+lrs) k x ('Bin lrs lrk lrx lrl lrr) 'Tip)
  BalanceL_Tip' _ k x ls lk lx lls llk llx lll llr lrs lrk lrx lrl lrr =
    'Bin (1+ls) lrk lrx ('Bin (1+lls+Size lrl) lk lx ('Bin lls llk llx lll llr) lrl) ('Bin (1+Size lrr) k x lrr 'Tip)

type family BalanceL_Tip k x l where
  BalanceL_Tip k x 'Tip = 'Bin 1 k x 'Tip 'Tip
  BalanceL_Tip k x ('Bin ls lk lx 'Tip 'Tip) = 'Bin 2 k x ('Bin ls lk lx 'Tip 'Tip) 'Tip
  BalanceL_Tip k x ('Bin ls lk lx 'Tip (Bin lrs lrk lrx lrl lrr)) = 'Bin 3 lrk lrx ('Bin 1 lk lx 'Tip 'Tip) ('Bin 1 k x 'Tip 'Tip)
  BalanceL_Tip k x ('Bin ls lk lx ('Bin lls llk llx lll llr) 'Tip) = 'Bin 3 lk lx ('Bin lls llk llx lll llr) ('Bin 1 k x 'Tip 'Tip)
  BalanceL_Tip k x ('Bin ls lk lx ('Bin lls llk llx lll llr) ('Bin lrs lrk lrx lrl lrr)) =
    BalanceL_Tip' (CmpNat lrs (Ratio * lls)) k x ls lk lx lls llk llx lll llr lrs lrk lrx lrl lrr

type family BalanceL_Bin'' cmp k x ls lk lx lls llk llx lll llr lrs lrk lrx lrl lrr rs rx rk rl rr where
  BalanceL_Bin'' 'LT k x ls lk lx lls llk llx lll llr lrs lrk lrx lrl lrr rs rx rk rl rr =
    'Bin (1+ls+rs) lk lx ('Bin lls llk llx lll llr) ('Bin (1+rs+lrs) k x ('Bin lrs lrk lrx lrl lrr) ('Bin rs rk rx rl rr))
  BalanceL_Bin'' _ k x ls lk lx lls llk llx lll llr lrs lrk lrx lrl lrr rs rx rk rl rr =
    'Bin (1+ls+rs) lrk lrx ('Bin (1+lls+Size lrl) lk lx ('Bin lls llk llx lll llr) lrl) ('Bin (1+rs+Size lrr) k x lrr ('Bin rs rk rx rl rr))

type family BalanceL_Bin' cmp k x ls lk lx ll lr rs rx rk rl rr where
  BalanceL_Bin' 'GT k x ls lk lx ('Bin lls llk llx lll llr) ('Bin lrs lrk lrx lrl lrr) rs rx rk rl rr =
    BalanceL_Bin'' (CmpNat lrs (Ratio * lls)) k x ls lk lx lls llk llx lll llr lrs lrk lrx lrl lrr rs rx rk rl rr
  BalanceL_Bin' _ k x ls lk lx ll lr rs rx rk rl rr = 'Bin (1+ls+rs) k x ('Bin ls lk lx ll lr) ('Bin rs rk rx rl rr)

type family BalanceL_Bin k x l rs rx rk rl rr where
  BalanceL_Bin k x 'Tip rs rx rk rl rr = 'Bin (1+rs) k x 'Tip ('Bin rs rk rx rl rr)
  BalanceL_Bin k x ('Bin ls lk lx ll lr) rs rx rk rl rr = BalanceL_Bin' (CmpNat ls (Delta * rs)) k x ls lk lx ll lr rs rx rk rl rr

type family BalanceL k x l r where
  BalanceL k x l 'Tip = BalanceL_Tip k x l
  BalanceL k x l ('Bin rs rk rx rl rr) = BalanceL_Bin k x l rs rx rk rl rr

type family BalanceR_Tip' cmp k x rs rk rx rls rlk rlx rll rlr rrs rrk rrx rrl rrr where
  BalanceR_Tip' 'LT k x rs rk rx rls rlk rlx rll rlr rrs rrk rrx rrl rrr =
    'Bin (1+rs) rk rx ('Bin (1+rls) k x 'Tip ('Bin rls rlk rlx rll rlr)) ('Bin rrs rrk rrx rrl rrr)
  BalanceR_Tip' _ k x rs rk rx rls rlk rlx rll rlr rrs rrk rrx rrl rrr =
    'Bin (1+rs) rlk rlx ('Bin (1+Size rll) k x 'Tip rll) ('Bin (1+rrs+Size rlr) rk rx rlr ('Bin rrs rrk rrx rrl rrr))

type family BalanceR_Tip k x r where
  BalanceR_Tip k x 'Tip = 'Bin 1 k x 'Tip 'Tip
  BalanceR_Tip k x ('Bin rs rk rx 'Tip 'Tip) = 'Bin 2 k x 'Tip ('Bin rs rk rx 'Tip 'Tip)
  BalanceR_Tip k x ('Bin rs rk rx 'Tip (Bin rrs rrk rrx rrl rrr)) = 'Bin 3 rk rx ('Bin 1 k x 'Tip 'Tip) ('Bin rrs rrk rrx rrl rrr)
  BalanceR_Tip k x ('Bin rs rk rx ('Bin rls rlk rlx rll rlr) 'Tip) = 'Bin 3 rlk rlx ('Bin 1 k x 'Tip 'Tip) ('Bin 1 rk rx 'Tip 'Tip)
  BalanceR_Tip k x ('Bin rs rk rx ('Bin rls rlk rlx rll rlr) ('Bin rrs rrk rrx rrl rrr)) =
    BalanceR_Tip' (CmpNat rls (Ratio * rrs)) k x rs rk rx rls rlk rlx rll rlr rrs rrk rrx rrl rrr

type family BalanceR_Bin'' cmp k x ls lk lx ll lr rs rk rx rls rlk rlx rll rlr rrs rrk rrx rrl rrr where
  BalanceR_Bin'' 'LT k x ls lk lx ll lr rs rk rx rls rlk rlx rll rlr rrs rrk rrx rrl rrr =
    'Bin (1+ls+rs) rk rx ('Bin (1+ls+rls) k x ('Bin ls lk lx ll lr) ('Bin rls rlk rlx rll rlr)) ('Bin rrs rrk rrx rrl rrr)
  BalanceR_Bin'' _ k x ls lk lx ll lr rs rk rx rls rlk rlx rll rlr rrs rrk rrx rrl rrr =
    'Bin (1+ls+rs) rlk rlx ('Bin (1+ls+Size rll) k x ('Bin ls lk lx ll lr) rll) ('Bin (1+rrs+Size rlr) rk rx rlr ('Bin rrs rrk rrx rrl rrr))

type family BalanceR_Bin' cmp k x ls lk lx ll lr rs rx rk rl rr where
  BalanceR_Bin' 'GT k x ls lk lx ll lr rs rk rx ('Bin rls rlk rlx rll rlr) ('Bin rrs rrk rrx rrl rrr) =
    BalanceR_Bin'' (CmpNat rls (Ratio * rrs)) k x ls lk lx ll lr rs rk rx rls rlk rlx rll rlr rrs rrk rrx rrl rrr
  BalanceR_Bin' _ k x ls lk lx ll lr rs rk rx rl rr = 'Bin (1+ls+rs) k x ('Bin ls lk lx ll lr) ('Bin rs rk rx rl rr)

type family BalanceR_Bin k x ls lk lx ll lr r where
  BalanceR_Bin k x ls lk lx ll lr 'Tip = 'Bin (1+ls) k x ('Bin ls lk lx ll lr) 'Tip
  BalanceR_Bin k x ls lk lx ll lr ('Bin rs rk rx rl rr) = BalanceR_Bin' (CmpNat rs (Delta * ls)) k x ls lk lx ll lr rs rk rx rl rr

type family BalanceR k x l r where
  BalanceR k x 'Tip r = BalanceR_Tip k x r
  BalanceR k x ('Bin ls lk lx ll lr) r = BalanceR_Bin k x ls lk lx ll lr r

type family Insert' cmp kx x sz ky z l r where
  Insert' 'LT kx x sz ky y l r = BalanceL ky y (Insert kx x l) r
  Insert' 'GT kx x sz ky y l r = BalanceR ky y l (Insert kx x r)
  Insert' 'EQ kx x sz ky y l r = Bin sz kx x l r

type family Insert kx x t where
  Insert kx x 'Tip = Singleton kx x
  Insert kx x ('Bin sz ky y l r) = Insert' (CmpSymbol kx ky) kx x sz ky y l r

type family MinViewSure' mv k x r where
  MinViewSure' ('MinView km xm l') k x r = 'MinView km xm (BalanceR k x l' r)

type family MinViewSure k x l r where
  MinViewSure k x 'Tip r = 'MinView k x r
  MinViewSure k x ('Bin _ kl xl ll lr) r = MinViewSure' (MinViewSure kl xl ll lr) k x r

type family MaxViewSure' mv k x l where
  MaxViewSure' ('MaxView km xm r') k x l = 'MaxView km xm (BalanceL k x l r')

type family MaxViewSure k x l r where
  MaxViewSure k x l 'Tip = 'MaxView k x l
  MaxViewSure k x l ('Bin _ kr xr rl rr) = MaxViewSure' (MaxViewSure kr xr rl rr) k x l

type family Glue'' mv r where
  Glue'' ('MaxView km m l') r = BalanceR km m l' r

type family Glue''' mv l where
  Glue''' ('MinView km m r') l = BalanceL km m l r'

type family Glue' cmp sl kl xl ll lr sr kr xr rl rr where
  Glue' 'GT sl kl xl ll lr sr kr xr rl rr = Glue'' (MaxViewSure kl xl ll lr) ('Bin sr kr xr rl rr)
  Glue' _   sl kl xl ll lr sr kr xr rl rr = Glue''' (MinViewSure kr xr rl rr) ('Bin sl kl xl ll lr)

type family Glue l r where
  Glue 'Tip r = r
  Glue l 'Tip = l
  Glue (Bin sl kl xl ll lr) (Bin sr kr xr rl rr) = Glue' (CmpNat sl sr) sl kl xl ll lr sr kr xr rl rr

type family Delete' cmp k kx x l r where
  Delete' 'LT k kx x l r = BalanceR kx x (Delete k l) r
  Delete' 'GT k kx x l r = BalanceL kx x l (Delete k r)
  Delete' 'EQ k kx x l r = Glue l r

type family Delete k t where
  Delete k 'Tip = 'Tip
  Delete k ('Bin _ kx x l r) = Delete' (CmpSymbol k kx) k kx x l r

type family InsertR' cmp kx x sz kz z l r where
  InsertR' 'LT kx x sz ky y l r = BalanceL ky y (Insert kx x l) r
  InsertR' 'GT kx x sz ky y l r = BalanceR ky y l (Insert kx x r)
  InsertR' 'EQ kx x sz ky y l r = Bin sz ky y l r

type family InsertR kx x t where
  InsertR kx x 'Tip = Singleton kx x
  InsertR kx x ('Bin sz ky y l r) = InsertR' (CmpSymbol kx ky) kx x sz ky y l r

type family InsertMax kx x t where
  InsertMax kx x 'Tip = Singleton kx x
  InsertMax kx x ('Bin _ ky y l r) = BalanceR ky y l (InsertMax kx x r)

type family InsertMin kx x t where
  InsertMin kx x 'Tip = Singleton kx x
  InsertMin kx x ('Bin _ ky y l r) = BalanceR ky y (InsertMin kx x l) r

type MkBin kx x l r = 'Bin (1 + Size l + Size r) kx x l r

type family Link' a b kx x sy ky y ly ry sz kz z lz rz where
  Link' 'LT _  kx x sy ky y ly ry sz kz z lz rz = BalanceL kz z (Link kx x ('Bin sy ky y ly ry) lz) rz
  Link' _  'LT kx x sy ky y ly ry sz kz z lz rz = BalanceR ky y ly (Link kx x ry ('Bin sz kz z lz rz))
  Link' _   _  kx x sy ky y ly ry sz kz z lz rz = MkBin kx x ('Bin sy ky y ly ry) ('Bin sz kz z lz rz)

type family Link kx x l r where
  Link kx x 'Tip r = InsertMin kx x r
  Link kx x l 'Tip = InsertMax kx x l
  Link kx x ('Bin sy ky y ly ry) ('Bin sz kz z lz rz) = Link' (CmpNat (Delta * sy) sz) (CmpNat (Delta * sz) sy) kx x sy ky y ly ry sz kz z lz rz

data Splitted a = Splitted (Dict a) (Dict a)

type family Split'' t kx x r where
  Split'' ('Splitted lt gt) kx x r = 'Splitted lt (Link kx x gt r)

type family Split''' t kx x l where
  Split''' ('Splitted lt gt) kx x l = 'Splitted (Link kx x l lt) gt

type family Split' cmp k kx x l r where
  Split' 'LT k kx x l r = Split'' (Split k l) kx x r
  Split' 'GT k kx x l r = Split''' (Split k r) kx x l
  Split' 'EQ k kx x l r = 'Splitted l r

type family Split k t where
  Split k 'Tip = 'Splitted 'Tip 'Tip
  Split k ('Bin _ kx x l r) = Split' (CmpSymbol k kx) k kx x l r

type family Union' t k1 x1 l1 r1 where
  Union' ('Splitted l2 r2) k1 x1 l1 r1 = Link k1 x1 (Union l1 l2) (Union r1 r2)

type family Union l r where
  Union t1 'Tip  = t1
  Union t1 ('Bin _ k x 'Tip 'Tip) = InsertR k x t1
  Union ('Bin _ k x 'Tip 'Tip) t2 = Insert k x t2
  Union 'Tip t2 = t2
  Union ('Bin _ k1 x1 l1 r1) t2 = Union' (Split k1 t2) k1 x1 l1 r1

type family ToAscList' t acc where
  ToAscList' 'Tip acc = acc
  ToAscList' ('Bin _ k x l r) acc = ToAscList' l ('(k, x) ': ToAscList' r acc)

type ToAscList t = ToAscList' t '[]
type Assocs t = ToAscList t

type family FromList l where
  FromList '[] = Empty
  FromList ('(k, x) ': r) = Insert k x (FromList r)

type family Keys' t acc where
  Keys' 'Tip acc = acc
  Keys' ('Bin _ k x l r) acc = Keys' l (k ': Keys' r acc)

type Keys t = Keys' t '[]


--
-- Sometimes the dictionary has to be in a canonical form for structural comparisons.
-- The inserts do not guarantee a unique form: the order of inserts matters.
-- Normalization creates such a distinct form.
--

type Normalize t = FromList (Assocs t)  -- there are more asymptotically efficient implementations possible


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

newtype Rec (t :: Dict Type) = Rec (HashMap Text Any)

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

delete :: KnownSymbol k => Proxy k -> Rec t -> Rec (Delete k t)
delete k (Rec m) = Rec $ HM.delete (T.pack $ symbolVal k) m

union :: Rec a -> Rec b -> Rec (Union a b)
union (Rec a) (Rec b) = Rec $ HM.union a b

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
