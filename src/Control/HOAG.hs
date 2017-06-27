{-# LANGUAGE TypeOperators, KindSignatures, DataKinds, PolyKinds, TypeFamilies, TypeInType #-}
{-# LANGUAGE TypeFamilyDependencies, ConstraintKinds, FlexibleContexts, FlexibleInstances, UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, GADTs, Rank2Types #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE Trustworthy #-}
module Control.HOAG
  ( Grammar(..), Nont(..), Prod(..), Child(..), Decl(..), Decls(..), EmptyGrammar
  , RuleId(..), Compile
  , assemble, assembleWith, compile, weave, eval, Program, Assembly, Weave
  , ValidChildInhType, ValidLhsSynType, ValidLocType, ValidChildType, ValidProdRef
  , GetChildren, GetInhAttrs, GetSynAttrs, GetLocAttrs
  , Expr(..), ExprTrans(..)
  , (∨), (∧), (≡), (≠), (¬), (<≡), (>≡), (<!), (!>)
  , NodeRef(..), ResolveAttrs, ResolveNodeRef, attrs, ValidAttrRef, (!)
  , Env, ProdCon, Module
  , ExprUnlift, exprLiftM, exprLift1
  , emptyModule,  declNont, declProd, declInh, declSyn, defChild, redefChild, defInh, redefInh
  , defLoc, redefLoc, defLhs, redefLhs, prod, aroundChild, reflChildren, this, (§§)
  , root, lhs, loc, genLabels, Proxy(Proxy)
  , RuleDefs((:=), (:+)), AliasPat((:*:)), rules, attributes, (?), (?:), (@?), (§), AttrDefs((:::)), inh, syn, (&:)
  , productions, (&|)
  , cons, nil, hd, tl, val, mkList, declList, mkMap, declMap, declSink
  ) where

import Control.Applicative
import Control.Exception hiding (TypeError)
import Control.Monad
import Control.Monad.Cont.Class
import Control.Monad.Except
import Control.Monad.Fail hiding(fail)
import qualified Control.Monad.Fail as F
import Control.Monad.IO.Class
import Control.Monad.Reader
import Control.Monad.RWS.Class
import Control.Monad.State.Class
import Control.Monad.Writer.Class
import Control.Monad.Zip
import Control.MonadFlow
import Data.Hashable
import Data.HashMap.Strict(HashMap)
import qualified Data.HashMap.Strict as HM
import Data.IntMap(IntMap)
import Data.Kind(Type, Constraint)
import Data.Map(Map)
import qualified Data.Map as M
import Data.Proxy
import Data.Semigroup hiding (Any)
import qualified Data.Semigroup as SG
import Data.Sequence(Seq)
import Data.Set(Set)
import Data.String
import Data.Text(Text)
import qualified Data.Text as T
import Data.Typeable
import Data.Type.Dict(Dict)
import qualified Data.Type.Assocs as A
import qualified Data.Type.Dict as D
import GHC.Exts
import GHC.TypeLits
import Language.Haskell.TH hiding (Type)
import Unsafe.Coerce


--
-- Grammar
--

type Grammar = Dict Nont
data Nont  = Nont (A.Dict Prod) (Dict Type) (Dict Type)
data Prod  = Prod (Dict Child) (Dict InternalType) (Dict InternalType) Type
data Child = Child Symbol (Dict InternalType)
data InternalType = InternalType Type Type


--
-- Decls
--

data Decl
  = NontDecl Symbol
  | ProdDecl Symbol Symbol Type
  | InhDecl Symbol Symbol Type
  | SynDecl Symbol Symbol Type

  | ChildDef Symbol Symbol Symbol Symbol
  | InhDef Symbol Symbol Symbol Symbol Type
  | LocDef Symbol Symbol Symbol Type
  | LhsDef Symbol Symbol Symbol Type

  | ChildReDef Symbol Symbol Symbol
  | InhReDef Symbol Symbol Symbol Symbol Type
  | LocReDef Symbol Symbol Symbol Type
  | LhsReDef Symbol Symbol Symbol Type

data Decls = SingleDecl Decl | ComposeDecls Decls Decls | EmptyDecls


type FlattenDecls ds = FlattenDecls' ds '[]

type family FlattenDecls' ds acc where
  FlattenDecls' ('SingleDecl d)     acc = d ': acc
  FlattenDecls' ('ComposeDecls l r) acc = FlattenDecls' l (FlattenDecls' r acc)
  FlattenDecls' 'EmptyDecls         acc = acc


--
-- Transformation of Decls To Grammar
--

type EmptyGrammar = D.Empty

type Compile (ds :: Decls) (init :: Grammar) = Compile' (FlattenDecls ds) init
type Compile' ds init = CompileCheck (Compile4 ds (Compile3 ds (Compile2 ds (Compile1 ds (Compile0 ds (Right init))))))

type family CompileCheck eg where
  CompileCheck ('Right g) = g
  CompileCheck ('Left e)  = TypeError e


--
-- Phase 0
--

type family Compile0 ds eg where
  Compile0 _                    ('Left e)  = 'Left e
  Compile0 ('NontDecl nt ': ds) ('Right g) = Compile0 ds (InsertEmptyNont nt g)
  Compile0 (_ ': ds)            eg         = Compile0 ds eg
  Compile0 '[]                  eg         = eg

type InsertEmptyNont nt g = InsertEmptyNont1 (D.Member nt g) nt g

type family InsertEmptyNont1 mb nt g where
  InsertEmptyNont1 'False nt g = 'Right (D.Insert nt ('Nont A.Empty D.Empty D.Empty) g)
  InsertEmptyNont1 'True  _  g = 'Right g  -- already exists: skip


--
-- Phase 1
--

type family Compile1 ds eg where
  Compile1 _                           ('Left e)  = 'Left e
  Compile1 ('ProdDecl nt p ty ': ds)   ('Right g) = Compile1 ds (InsertEmptyProd nt p ty g)
  Compile1 ('InhDecl nt attr tp ': ds) ('Right g) = Compile1 ds (InsertInhAttr nt attr tp g)
  Compile1 ('SynDecl nt attr tp ': ds) ('Right g) = Compile1 ds (InsertSynAttr nt attr tp g)
  Compile1 (_ ': ds)                   eg         = Compile1 ds eg
  Compile1 '[]                         eg         = eg


type InsertEmptyProd nt p ty g = InsertEmptyProd0 (D.Lookup nt g) nt p ty g

type family InsertEmptyProd0 mbNont nt p ty g where
  InsertEmptyProd0 ('Just ('Nont ps is ss)) nt p ty g
    = InsertEmptyProd1 (A.Member p ps) ps is ss nt p ty g
  InsertEmptyProd0 'Nothing nt p _ _
    = 'Left ('Text "Undeclared nonterminal " :<>: ShowType nt :<>: 'Text " at production declaration " :<>: ShowType p)

type family InsertEmptyProd1 mb ps is ss nt p ty g where
  InsertEmptyProd1 'False ps is ss nt p ty g = 'Right (D.Insert nt ('Nont (A.Insert p (EmptyProd ty) ps) is ss) g)
  InsertEmptyProd1 'True  _  _  _  nt p _  _ = 'Left ('Text "Duplicate declaration of production " :<>: ShowType p :<>: 'Text " of nonterminal " :<>: ShowType nt)

type EmptyProd ty = 'Prod D.Empty D.Empty D.Empty ty


type InsertInhAttr nt attr tp g = InsertInhAttr0 (D.Lookup nt g) nt attr tp g

type family InsertInhAttr0 mbNont nt attr tp g where
  InsertInhAttr0 ('Just ('Nont ps is ss)) nt attr tp g
    = InsertInhAttr1 (D.Lookup attr is) ps is ss nt attr tp g
  InsertInhAttr0 'Nothing nt attr tp _
      = 'Left ('Text "Undeclared nonterminal " :<>: ShowType nt :<>: 'Text " at its inherited attribute declaration " :<>: ShowType attr)

type family InsertInhAttr1 mbAttr ps is ss nt attr tp g where
  InsertInhAttr1 'Nothing ps is ss nt attr tp g
    = 'Right (D.Insert nt ('Nont ps (D.Insert attr tp is) ss) g)
  InsertInhAttr1 ('Just _) _ _ _ nt attr _ _
    = 'Left ('Text "Duplicate declaration of inherited attribute " :<>: ShowType attr :<>: 'Text " of nonterminal " :<>: ShowType nt)


type InsertSynAttr nt attr tp g = InsertSynAttr0 (D.Lookup nt g) nt attr tp g

type family InsertSynAttr0 mbNont nt attr tp g where
  InsertSynAttr0 ('Just ('Nont ps is ss)) nt attr tp g
    = InsertSynAttr1 (D.Lookup attr ss) ps is ss nt attr tp g
  InsertSynAttr0 'Nothing nt attr tp _
      = 'Left ('Text "Undeclared nonterminal " :<>: ShowType nt :<>: 'Text " at its synthesized attribute declaration " :<>: ShowType attr)

type family InsertSynAttr1 mbAttr ps is ss nt attr tp g where
  InsertSynAttr1 'Nothing ps is ss nt attr tp g
    = 'Right (D.Insert nt ('Nont ps is (D.Insert attr tp ss)) g)
  InsertSynAttr1 ('Just _) _ _ _ nt attr _ _
    = 'Left ('Text "Duplicate declaration of synthesized attribute " :<>: ShowType attr :<>: 'Text " of nonterminal " :<>: ShowType nt)


--
-- Phase 2
--

type family Compile2 ds eg where
   Compile2 _                            ('Left e)  = 'Left e
   Compile2 ('ChildDef nt p c nt' ': ds) ('Right g) = Compile2 ds (InsertChild nt p c nt' g)
   Compile2 ('LocDef nt p attr ty ': ds) ('Right g) = Compile2 ds (InsertLocDecl nt p attr ty g)
   Compile2 (_ ': ds)                    eg         = Compile2 ds eg
   Compile2 '[]                          eg         = eg


type InsertChild nt p c nt' g = InsertChild0 (D.Lookup nt g) nt p c nt' g

type family InsertChild0 mbNont nt p c nt' g where
  InsertChild0 ('Just ('Nont ps is ss)) nt p c nt' g
    = InsertChild1 (A.Lookup p ps) ps is ss nt p c nt' g
  InsertChild0 'Nothing nt p c _ _
    = 'Left ('Text "Undeclared nonterminal " :<>: ShowType nt :<>: 'Text " at child declaration " :<>: ShowType c :<>: 'Text " of its production " :<>: ShowType p)

type family InsertChild1 mbProd ps is ss nt p c nt' g where
  InsertChild1 'Nothing ps is ss nt p c nt' g
    = 'Left ('Text "Undeclared production " :<>: ShowType p :<>: 'Text " of nonterminal " :<>: ShowType nt :<>: 'Text " at its child declaration " :<>: ShowType c)
  InsertChild1 ('Just ('Prod cs locs syns pty)) ps is ss nt p c nt' g
    = InsertChild2 (D.Lookup c cs) cs locs syns pty ps is ss nt p c nt' g

type family InsertChild2 mbChild cs locs syns pty ps is ss nt p c nt' g where
  InsertChild2 'Nothing cs locs syns pty ps is ss nt p c nt' g
    = 'Right (D.Insert nt ('Nont (A.Insert p ('Prod (D.Insert c (EmptyChild nt') cs) locs syns pty) ps) is ss) g)
  InsertChild2 ('Just _) _ _ _ _ _ _ _ nt p c _ _
    = 'Left ('Text "Duplicate child declaration " :<>: ShowType c :<>: 'Text " of production " :<>: ShowType p :<>: 'Text " of nonterminal " :<>: ShowType nt)

type EmptyChild nt = 'Child nt D.Empty


type InsertLocDecl nt p attr ty g = InsertLocDecl0 (D.Lookup nt g) nt p attr ty g

type family InsertLocDecl0 mbNont nt p attr ty g where
  InsertLocDecl0 ('Just ('Nont ps is ss)) nt p attr ty g
    = InsertLocDecl1 (A.Lookup p ps) ps is ss nt p attr ty g
  InsertLocDecl0 'Nothing nt p attr _ _
    = 'Left ('Text "Undeclared nonterminal " :<>: ShowType nt :<>: 'Text " at loc definition " :<>: ShowType attr :<>: 'Text " of its production " :<>: ShowType p)

type family InsertLocDecl1 mbProd ps is ss nt p attr ty g where
  InsertLocDecl1 ('Just ('Prod cs locs syns pty)) ps is ss nt p attr ty g
    = InsertLocDecl2 (D.Lookup attr locs) cs locs syns pty ps is ss nt p attr ty g
  InsertLocDecl1 'Nothing _ _ _ nt p attr _ g
    = 'Left ('Text "Undeclared production " :<>: ShowType p :<>: 'Text " of nonterminal " :<>: ShowType nt :<>: 'Text " at its loc definition " :<>: ShowType attr)

type family InsertLocDecl2 mbAttr cs locs syns pty ps is ss nt p attr ty g where
  InsertLocDecl2 'Nothing cs locs syns pty ps is ss nt p attr ty g
    = 'Right (D.Insert nt ('Nont (A.Insert p ('Prod cs (D.Insert attr ('InternalType ty ty) locs) syns pty) ps) is ss) g)
  InsertLocDecl2 ('Just _) _ _ _ _ _ _ _ nt p attr _ _
    = 'Left ('Text "Duplicate local attribute definition " :<>: ShowType attr :<>: 'Text " of production " :<>: ShowType p :<>: 'Text " of nonterminal " :<>: ShowType nt)


--
-- Checks for the left-hand-side of rules
--


type CheckSynAttr nt attr g = CheckSynAttr1 (D.Lookup nt g) nt attr

type family CheckSynAttr1 mb nt attr where
  CheckSynAttr1 ('Just ('Nont _ _ syns)) nt attr = CheckSynAttr2 (D.Lookup attr syns) nt attr
  CheckSynAttr1 'Nothing _ _ = 'Just ('Text "Internal error")

type family CheckSynAttr2 mb nt attr where
  CheckSynAttr2 ('Just _) nt attr = 'Nothing
  CheckSynAttr2 'Nothing  nt attr = 'Just ('Text "Undeclared synthesized attribute " :<>: ShowType attr :<>: 'Text " of nonterminal " :<>: ShowType nt)


type CheckInhTy nt attr g = CheckInhTy1 (D.Lookup nt g) nt attr

type family CheckInhTy1 mb nt attr where
  CheckInhTy1 ('Just ('Nont _ inhs _)) nt attr = CheckInhTy2 (D.Lookup attr inhs) nt attr
  CheckInhTy1 'Nothing _ _ = 'Just ('Text "Internal error")

type family CheckInhTy2 mb nt attr where
  CheckInhTy2 ('Just _) _ _    = 'Nothing
  CheckInhTy2 'Nothing nt attr = 'Just ('Text "Undeclared inherited attribute " :<>: ShowType attr :<>: 'Text " of nonterminal " :<>: ShowType nt)


--
-- Phase 2
--

type family Compile3 ds eg where
   Compile3 _                               ('Left e)  = 'Left e
   Compile3 ('InhDef nt p c attr ty  ': ds) ('Right g) = Compile3 ds (InsertInhDef nt p c attr ty g)
   Compile3 ('LhsDef nt p attr ty    ': ds) ('Right g) = Compile3 ds (InsertLhsDef nt p attr ty g)
   Compile3 (_ ': ds)                       eg         = Compile3 ds eg
   Compile3 '[]                             eg         = eg


type InsertLhsDef nt p attr ty g = InsertLhsDef0 (D.Lookup nt g) nt p attr ty g

type family InsertLhsDef0 mbNont nt p attr ty g where
  InsertLhsDef0 ('Just ('Nont ps is ss)) nt p attr ty g
    = InsertLhsDef1 (A.Lookup p ps) ps is ss nt p attr ty g
  InsertLhsDef0 'Nothing nt p attr _ _
    = 'Left ('Text "Undeclared nonterminal " :<>: ShowType nt :<>: 'Text " at lhs definition " :<>: ShowType attr :<>: 'Text " of its production " :<>: ShowType p)

type family InsertLhsDef1 mbProd ps is ss nt p attr ty g where
  InsertLhsDef1 ('Just ('Prod cs locs syns pty)) ps is ss nt p attr ty g
    = InsertLhsDef2 (D.Lookup attr syns) (CheckSynAttr nt attr g) cs locs syns pty ps is ss nt p attr ty g
  InsertLhsDef1 'Nothing _ _ _ nt p attr _ g
    = 'Left ('Text "Undeclared production " :<>: ShowType p :<>: 'Text " of nonterminal " :<>: ShowType nt :<>: 'Text " at its lhs definition " :<>: ShowType attr)

type family InsertLhsDef2 mbAttr mbErrDef cs locs syns pty ps is ss nt p attr ty g where
  InsertLhsDef2 'Nothing 'Nothing cs locs syns pty ps is ss nt p attr ty g
    = 'Right (D.Insert nt ('Nont (A.Insert p ('Prod cs locs (D.Insert attr ('InternalType ty ty) syns) pty) ps) is ss) g)
  InsertLhsDef2 ('Just _) _ _ _ _ _ _ _ _ nt p attr _ _
    = 'Left ('Text "Duplicate synthesized attribute definition " :<>: ShowType attr :<>: 'Text " of production " :<>: ShowType p :<>: 'Text " of nonterminal " :<>: ShowType nt)
  InsertLhsDef2 _ ('Just e) _ _ _ _ _ _ _ nt p attr _ _
    = 'Left (e :<>: 'Text " at synthesized attribute definition " :<>: ShowType attr :<>: 'Text " of production " :<>: ShowType p :<>: 'Text " of nonterminal " :<>: ShowType nt)


type InsertInhDef nt p c attr ty g = InsertInhDef0 (D.Lookup nt g) nt p c attr ty g

type family InsertInhDef0 mbNont nt p c attr ty g where
  InsertInhDef0 ('Just ('Nont ps is ss)) nt p c attr ty g
    = InsertInhDef1 (A.Lookup p ps) ps is ss nt p c attr ty g
  InsertInhDef0 'Nothing nt p c attr _ _
    = 'Left ('Text "Undeclared nonterminal " :<>: ShowType nt :<>: 'Text " at inherited definition " :<>: ShowType attr :<>: 'Text " of child " :<>: ShowType c :<>: 'Text " of its production " :<>: ShowType p)

type family InsertInhDef1 mbProd ps is ss nt p c attr ty g where
  InsertInhDef1 ('Just ('Prod cs locs syns pty)) ps is ss nt p c attr ty g
    = InsertInhDef2 (D.Lookup c cs) cs locs syns pty ps is ss nt p c attr ty g
  InsertInhDef1 'Nothing _ _ _ nt p c attr _ g
    = 'Left ('Text "Undeclared production " :<>: ShowType p :<>: 'Text " of nonterminal " :<>: ShowType nt :<>: 'Text " at inherited definition " :<>: ShowType attr :<>: 'Text " of child " :<>: ShowType c :<>: 'Text " of its production " :<>: ShowType p)

type family InsertInhDef2 mbChild cs locs syns pty ps is ss nt p c attr ty g where
  InsertInhDef2 ('Just ('Child nt' inhs)) cs locs syns pty ps is ss nt p c attr ty g
    = InsertInhDef3 (D.Lookup attr inhs) (CheckInhTy nt' attr g) nt' inhs cs locs syns pty ps is ss nt p c attr ty g
  InsertInhDef2 'Nothing _ _ _ _ _ _ _ nt p c attr _ _
    = 'Left ('Text "Undeclared child " :<>: ShowType c :<>: 'Text " at its inherited attribute definition " :<>: ShowType attr :<>: 'Text " of production " :<>: ShowType p :<>: 'Text " of nonterminal " :<>: ShowType nt)

type family InsertInhDef3 mbAttr mbErr nt' inhs cs locs syns pty ps is ss nt p c attr ty g where
  InsertInhDef3 'Nothing 'Nothing nt' inhs cs locs syns pty ps is ss nt p c attr ty g
    = 'Right (D.Insert nt ('Nont (A.Insert p ('Prod (D.Insert c ('Child nt' (D.Insert attr ('InternalType ty ty) inhs)) cs) locs syns pty) ps) is ss) g)
  InsertInhDef3 ('Just _) _ _ _ _ _ _ _ _ _ _ nt p c attr _ _
    = 'Left ('Text "Duplicate inherited attribute definition " :<>: ShowType attr :<>: 'Text " of its child " :<>: ShowType c :<>: 'Text " of production " :<>: ShowType p :<>: 'Text " of nonterminal " :<>: ShowType nt)
  InsertInhDef3 _ ('Just e) _ _ _ _ _ _ _ _ _ nt p c attr _ _
    = 'Left (e :<>: 'Text " at inherited attribute definition " :<>: ShowType attr :<>: 'Text " of child " :<>: ShowType c :<>: 'Text " of production " :<>: ShowType p :<>: 'Text " of nonterminal " :<>: ShowType nt)


--
-- Phase 4
--

type family Compile4 ds eg where
   Compile4 _                                 ('Left e)  = 'Left e
   Compile4 ('InhReDef nt p c attr ty  ': ds) ('Right g) = Compile4 ds (InsertInhReDef nt p c attr ty g)
   Compile4 ('LhsReDef nt p attr ty    ': ds) ('Right g) = Compile4 ds (InsertLhsReDef nt p attr ty g)
   Compile4 ('LocReDef nt p attr ty    ': ds) ('Right g) = Compile4 ds (InsertLocReDef nt p attr ty g)
   Compile4 ('ChildReDef nt p c        ': ds) ('Right g) = Compile4 ds (InsertChildReDef nt p c g)
   Compile4 (_ ': ds)                         eg         = Compile4 ds eg
   Compile4 '[]                               eg         = eg


type InsertLocReDef nt p attr ty g = InsertLocReDef0 (D.Lookup nt g) nt p attr ty g

type family InsertLocReDef0 mbNont nt p attr ty g where
  InsertLocReDef0 ('Just ('Nont ps is ss)) nt p attr ty g
    = InsertLocReDef1 (A.Lookup p ps) ps is ss nt p attr ty g
  InsertLocReDef0 'Nothing nt p attr _ _
      = 'Left ('Text "Undeclared nonterminal " :<>: ShowType nt :<>: 'Text " at loc redefinition " :<>: ShowType attr :<>: 'Text " of its production " :<>: ShowType p)

type family InsertLocReDef1 mbProd ps is ss nt p attr ty g where
  InsertLocReDef1 ('Just ('Prod cs locs syns pty)) ps is ss nt p attr ty g
    = InsertLocReDef2 (D.Lookup attr locs) cs locs syns pty ps is ss nt p attr ty g
  InsertLocReDef1 'Nothing _ _ _ nt p attr _ g
    = 'Left ('Text "Undeclared production " :<>: ShowType p :<>: 'Text " of nonterminal " :<>: ShowType nt :<>: 'Text " of its loc redefinition " :<>: ShowType attr)

type family InsertLocReDef2 mbAttr cs locs syns pty ps is ss nt p attr ty g where
  InsertLocReDef2 ('Just ('InternalType _ ty0)) cs locs syns pty ps is ss nt p attr ty g
    = 'Right (D.Insert nt ('Nont (A.Insert p ('Prod cs (D.Insert attr ('InternalType ty ty0) locs) syns pty) ps) is ss) g)
  InsertLocReDef2 'Nothing _ _ _ _ _ _ _ nt p attr _ _
    = 'Left ('Text "Undefined local attribute at local redefinition of " :<>: ShowType attr :<>: 'Text " of production " :<>: ShowType p :<>: 'Text " of nonterminal " :<>: ShowType nt)


type InsertLhsReDef nt p attr ty g = InsertLhsReDef0 (D.Lookup nt g) nt p attr ty g

type family InsertLhsReDef0 mbNont nt p attr ty g where
  InsertLhsReDef0 ('Just ('Nont ps is ss)) nt p attr ty g
    = InsertLhsReDef1 (A.Lookup p ps) ps is ss nt p attr ty g
  InsertLhsReDef0 'Nothing nt p attr _ _
    = 'Left ('Text "Undeclared nonterminal " :<>: ShowType nt :<>: 'Text " at lhs redefinition " :<>: ShowType attr :<>: 'Text " of its production " :<>: ShowType p)

type family InsertLhsReDef1 mbProd ps is ss nt p attr ty g where
  InsertLhsReDef1 ('Just ('Prod cs locs syns pty)) ps is ss nt p attr ty g
    = InsertLhsReDef2 (D.Lookup attr syns) (CheckSynAttr nt attr g) cs locs syns pty ps is ss nt p attr ty g
  InsertLhsReDef1 'Nothing _ _ _ nt p attr _ g
    = 'Left ('Text "Undeclared production " :<>: ShowType p :<>: 'Text " of nonterminal " :<>: ShowType nt :<>: 'Text " at lhs redefinition " :<>: ShowType attr :<>: 'Text " of its production " :<>: ShowType p)

type family InsertLhsReDef2 mbAttr mbErrDef cs locs syns pty ps is ss nt p attr ty g where
  InsertLhsReDef2 (Just ('InternalType _ ty')) 'Nothing cs locs syns pty ps is ss nt p attr ty g
    = 'Right (D.Insert nt ('Nont (A.Insert p ('Prod cs locs (D.Insert attr ('InternalType ty ty') syns) pty) ps) is ss) g)
  InsertLhsReDef2 'Nothing _ _ _ _ _ _ _ _ nt p attr _ _
    = 'Left ('Text "Undefined synthesized attribute at synthesized redefinition of " :<>: ShowType attr :<>: 'Text " of production " :<>: ShowType p :<>: 'Text " of nonterminal " :<>: ShowType nt)
  InsertLhsReDef2 _ ('Just e) _ _ _ _ _ _ _ nt p attr _ _
    = 'Left (e :<>: 'Text " at synthesized attribute redefinition of " :<>: ShowType attr :<>: 'Text " of production " :<>: ShowType p :<>: 'Text " of nonterminal " :<>: ShowType nt)


type InsertInhReDef nt p c attr ty g = InsertInhReDef0 (D.Lookup nt g) nt p c attr ty g

type family InsertInhReDef0 mbNont nt p c attr ty g where
  InsertInhReDef0 ('Just ('Nont ps is ss)) nt p c attr ty g
    = InsertInhReDef1 (A.Lookup p ps) ps is ss nt p c attr ty g
  InsertInhReDef0 'Nothing nt p c attr _ _
    = 'Left ('Text "Undeclared nonterminal " :<>: ShowType nt :<>: 'Text " at inherited redefinition of " :<>: ShowType attr :<>: 'Text " of child " :<>: ShowType c :<>: 'Text " of its production " :<>: ShowType p)

type family InsertInhReDef1 mbProd ps is ss nt p c attr ty g where
  InsertInhReDef1 ('Just ('Prod cs locs syns pty)) ps is ss nt p c attr ty g
    = InsertInhReDef2 (D.Lookup c cs) cs locs syns pty ps is ss nt p c attr ty g
  InsertInhReDef1 'Nothing _ _ _ nt p c attr _ g
    = 'Left ('Text "Undeclared production " :<>: ShowType p :<>: 'Text " of nonterminal " :<>: ShowType nt :<>: 'Text " at its inh redefinition " :<>: ShowType attr :<>: 'Text " of child " :<>: ShowType c)

type family InsertInhReDef2 mbChild cs locs syns pty ps is ss nt p c attr ty g where
  InsertInhReDef2 ('Just ('Child nt' inhs)) cs locs syns pty ps is ss nt p c attr ty g
    = InsertInhReDef3 (D.Lookup attr inhs) (CheckInhTy nt' attr g) nt' inhs cs locs syns pty ps is ss nt p c attr ty g
  InsertInhReDef2 'Nothing _ _ _ _ _ _ _ nt p c attr _ _
    = 'Left ('Text "Undeclared child " :<>: ShowType c :<>: 'Text " at inherited attribute redefinition " :<>: ShowType attr :<>: 'Text " of production " :<>: ShowType p :<>: 'Text " of nonterminal " :<>: ShowType nt)

type family InsertInhReDef3 mbAttr mbErr nt' inhs cs locs syns pty ps is ss nt p c attr ty g where
  InsertInhReDef3 ('Just ('InternalType _ ty')) 'Nothing nt' inhs cs locs syns pty ps is ss nt p c attr ty g
    = 'Right (D.Insert nt ('Nont (A.Insert p ('Prod (D.Insert c ('Child nt' (D.Insert attr ('InternalType ty ty') inhs)) cs) locs syns pty) ps) is ss) g)
  InsertInhReDef3 'Nothing _ _ _ _ _ _ _ _ _ _ nt p c attr _ _
    = 'Left ('Text "Undefined inherited attribute at inherited redefinition of " :<>: ShowType attr :<>: 'Text " of child " :<>: ShowType c :<>: 'Text " of production " :<>: ShowType p :<>: 'Text " of nonterminal " :<>: ShowType nt)
  InsertInhReDef3 _ ('Just e) _ _ _ _ _ _ _ _ _ nt p c attr _ _
    = 'Left (e :<>: 'Text " at inherited attribute redefinition " :<>: ShowType attr :<>: 'Text " of child " :<>: ShowType c :<>: 'Text " of production " :<>: ShowType p :<>: 'Text " of nonterminal " :<>: ShowType nt)


type InsertChildReDef nt p c g = InsertChildReDef0 (D.Lookup nt g) nt p c g

type family InsertChildReDef0 mbNont nt p c g where
  InsertChildReDef0 ('Just ('Nont ps _ _)) nt p c g
    = InsertChildReDef1 (A.Lookup p ps) nt p c g
  InsertChildReDef0 'Nothing nt p c _
    = 'Left ('Text "Undeclared nonterminal " :<>: ShowType nt :<>: 'Text " at child redefinition " :<>: ShowType c :<>: 'Text " of its production " :<>: ShowType p)

type family InsertChildReDef1 mbProd nt p c g where
  InsertChildReDef1 ('Just ('Prod cs _ _ _)) nt p c g
    = InsertChildReDef2 (D.Lookup c cs) nt p c g
  InsertChildReDef1 'Nothing nt p c _
    = 'Left ('Text "Undeclared production " :<>: ShowType p :<>: 'Text " of nonterminal " :<>: ShowType nt :<>: 'Text " at its child redefinition " :<>: ShowType c)

type family InsertChildReDef2 mbChild nt p c g where
  InsertChildReDef2 ('Just ('Child _ _)) _ _ _ g
    = 'Right g
  InsertChildReDef2 'Nothing nt p c _
    = 'Left ('Text "Undeclared child at child redefinition " :<>: ShowType c :<>: 'Text " of production " :<>: ShowType p :<>: 'Text " of nonterminal " :<>: ShowType nt)


--
-- Type checking
--

type GetProd nt p g = GetProd' (D.Find nt g) p
type family GetProd' nt p where
  GetProd' ('Nont ps _ _) p = A.Find p ps

type GetChild nt p c g = GetChild' (GetProd nt p g) c
type family GetChild' p c where
  GetChild' ('Prod cs _ _ _) c = D.Find c cs

type GetChildNt nt p c g = GetChildNt' (GetChild nt p c g)
type family GetChildNt' c where
  GetChildNt' ('Child nt _) = nt

type ValidChildType (g :: Grammar) (nt :: Symbol) (p :: Symbol) (c :: Symbol) (nt' :: Symbol) = GetChildNt nt p c g ~ nt'


type GetChildren nt p g = GetChildren1 (GetProd nt p g)

type family GetChildren1 p where
  GetChildren1 ('Prod cs _ _ _) = GetChildren2 (D.Assocs cs)

type family GetChildren2 cs where
  GetChildren2 ('(c , 'Child nt _) ': cs) = '(c, nt) ': GetChildren2 cs
  GetChildren2 '[] = '[]


type GetProdType nt p g = GetProdType1 (GetProd nt p g)

type family GetProdType1 prod where
  GetProdType1 ('Prod _ _ _ pty) = pty


type GetActualChildInhType nt p c attr g = GetActualChildInhType' (D.Find (GetChildNt nt p c g) g) attr
type family GetActualChildInhType' nt attr where
  GetActualChildInhType' ('Nont _ inhs _) attr = D.Find attr inhs

type GetInternalChildInhType nt p c attr g = GetInternalChildInhType' (GetChild nt p c g) attr
type family GetInternalChildInhType' prod attr where
  GetInternalChildInhType' ('Child _ inhs) attr =  D.Find attr inhs

type family ValidChildInhType (redef :: Bool) (g :: Grammar) (nt :: Symbol) (p :: Symbol) (c :: Symbol) (attr :: Symbol) (a :: Type) (b :: Type) :: Constraint where
  ValidChildInhType 'False g nt p c attr a _ = ValidInternalType (GetInternalChildInhType nt p c attr g) (GetActualChildInhType nt p c attr g) a
  ValidChildInhType 'True  g nt p c attr a b = GetInternalChildInhType nt p c attr g ~ 'InternalType b a

type GetActualLhsSynType nt attr g = GetActualLhsSynType' (D.Find nt g) attr
type family GetActualLhsSynType' nont attr where
  GetActualLhsSynType' ('Nont _ _ syns) attr = D.Find attr syns

type GetInternalLhsSynType nt p attr g = GetInternalLhsSynType' (GetProd nt p g) attr
type family GetInternalLhsSynType' prod attr where
  GetInternalLhsSynType' ('Prod _ _ syns _) attr =  D.Find attr syns

type family ValidLhsSynType (redef :: Bool) (g :: Grammar) (nt :: Symbol) (p :: Symbol) (attr :: Symbol) (a :: Type) (b :: Type) :: Constraint where
  ValidLhsSynType 'False g nt p attr a _ = ValidInternalType (GetInternalLhsSynType nt p attr g) (GetActualLhsSynType nt attr g) a
  ValidLhsSynType 'True  g nt p attr a b = GetInternalLhsSynType nt p attr g ~ 'InternalType b a

type family ValidInternalType (inty :: InternalType) (b :: Type) (a :: Type) :: Constraint where
  ValidInternalType ('InternalType b a) b' a' = (a' ~ a, b' ~ b)


type family ValidLocType (redef :: Bool) (g :: Grammar) (nt :: Symbol) (p :: Symbol) (attr :: Symbol) (a :: Type) (b :: Type) :: Constraint where
  ValidLocType 'False _ _  _ _    _ _ = ()
  ValidLocType 'True  g nt p attr a b = GetLocType nt p attr g ~ ('InternalType b a)

type GetLocType nt p attr g = GetLocType1 (GetProd nt p g) attr

type family GetLocType1 prod attr where
  GetLocType1 ('Prod _ locs _ _) attr = D.Find attr locs


type ValidProdRef (nt :: Symbol) (p :: Symbol) (g :: Grammar) (a :: Type) = ValidProdRef1 (D.Lookup nt g) nt p ~ a

type family ValidProdRef1 mb nt p where
  ValidProdRef1 ('Just ('Nont ps _ _)) nt p = ValidProdRef2 (A.Lookup p ps) nt p
  ValidProdRef1 'Nothing               nt _ = TypeError ('Text "Undeclared nonterminal " :<>: ShowType nt)

type family ValidProdRef2 mb nt p where
  ValidProdRef2 ('Just ('Prod _ _ _ a)) _  _ = a
  ValidProdRef2 'Nothing                nt p = TypeError ('Text "Undeclared production " :<>: ShowType p :<>: 'Text " of nonterminal " :<>: ShowType nt)


type GetInhAttrs (nt :: Symbol) (g :: Grammar) = GetInhAttrs1 (D.Lookup nt g) nt

type family GetInhAttrs1 mb nt where
  GetInhAttrs1 ('Just ('Nont _ inhs _)) _  = inhs
  GetInhAttrs1 'Nothing                 nt = TypeError ('Text "Undeclared nonterminal " :<>: ShowType nt)

type GetSynAttrs nt g = GetSynAttrs1 (D.Lookup nt g) nt

type family GetSynAttrs1 mb nt where
  GetSynAttrs1 ('Just ('Nont _ _ syns)) _  = syns
  GetSynAttrs1 'Nothing                 nt = TypeError ('Text "Undeclared nonterminal " :<>: ShowType nt)


type GetLocAttrs (nt :: Symbol) (p :: Symbol) (g :: Grammar) = GetLocAttrs1 (D.Lookup nt g) nt p

type family GetLocAttrs1 mb nt p where
  GetLocAttrs1 ('Just ('Nont ps _ _)) nt p = GetLocAttrs2 (A.Lookup p ps) nt p
  GetLocAttrs1 'Nothing               nt _ = TypeError ('Text "Undeclared nonterminal " :<>: ShowType nt)

type family GetLocAttrs2 mb nt p where
  GetLocAttrs2 ('Just ('Prod _ locs _ _)) _  _ = locs
  GetLocAttrs2 'Nothing                   nt p = TypeError ('Text "Undeclared production " :<>: ShowType p :<>: 'Text " of nonterminal " :<>: ShowType nt)


type GetChildAttrs (nt :: Symbol) (p :: Symbol) (c :: Symbol) (g :: Grammar) = GetChildAttrs1 (D.Lookup nt g) nt p c g

type family GetChildAttrs1 mb nt p c g where
  GetChildAttrs1 ('Just ('Nont ps _ _)) nt p c g = GetChildAttrs2 (A.Lookup p ps) nt p c g
  GetChildAttrs1 'Nothing               nt _ _ _ = TypeError ('Text "Undeclared nonterminal " :<>: ShowType nt)

type family GetChildAttrs2 mb nt p c g where
  GetChildAttrs2 ('Just ('Prod cs _ _ _)) nt p c g = GetChildAttrs3 (D.Lookup c cs) nt p c g
  GetChildAttrs2 'Nothing                 nt p _ _ = TypeError ('Text "Undeclared production " :<>: ShowType p :<>: 'Text " of nonterminal " :<>: ShowType nt)

type family GetChildAttrs3 mb nt p c g where
  GetChildAttrs3 ('Just ('Child nt' _)) _  _ _ g = GetSynAttrs nt' g
  GetChildAttrs3 'Nothing               nt p c _ = TypeError ('Text "Undeclared child " :<>: ShowType c :<>: 'Text " of production " :<>: ShowType p :<>: 'Text " of nonterminal " :<>: ShowType nt)


--
-- Rule Ids
--

data RuleId = LhsRuleId Text | InhRuleId Text Text | LocRuleId Text | ChildRuleId Text
  deriving (Eq, Ord)

instance Hashable RuleId where
  hash (LhsRuleId a)   = hashWithSalt 109 a
  hash (InhRuleId c a) = hashWithSalt (hashWithSalt 277 c) a
  hash (LocRuleId a)   = hashWithSalt 443 a
  hash (ChildRuleId c) = hashWithSalt 661 c
  hashWithSalt s r = hashWithSalt s (hash r)

instance Show RuleId where
  show (LhsRuleId a)   = "lhs."   ++ show a
  show (InhRuleId c a) = show c   ++ "." ++ show a
  show (LocRuleId a)   = "loc."   ++ show a
  show (ChildRuleId c) = "child " ++ show c

childRuleKey :: KnownSymbol child => Proxy child -> RuleId
childRuleKey child = ChildRuleId $ T.pack $ symbolVal child

inhRuleKey :: (KnownSymbol child, KnownSymbol attr) => Proxy child -> Proxy attr -> RuleId
inhRuleKey child attr = InhRuleId (T.pack $ symbolVal child) (T.pack $ symbolVal attr)

locRuleKey :: KnownSymbol attr => Proxy attr -> RuleId
locRuleKey attr = LocRuleId $ T.pack $ symbolVal attr

lhsRuleKey :: KnownSymbol attr => Proxy attr -> RuleId
lhsRuleKey attr = LhsRuleId $ T.pack $ symbolVal attr


--
-- Expr (rhs of rules)
--

newtype Expr (nt :: Symbol) (p :: Symbol) (g :: Grammar) (m :: Type -> Type) (a :: Type) = Expr { unExpr :: ReaderT (Env m nt p g) m a }
type ExprTrans nt p g m a b = Expr nt p g m a -> Expr nt p g m b

instance Functor m => Functor (Expr nt p g m) where
  fmap f (Expr m) = Expr (fmap f m)

instance Applicative m => Applicative (Expr nt p g m) where
  pure = Expr . pure
  (Expr p) <*> (Expr q) = Expr $ p <*> q

instance Alternative m => Alternative (Expr nt p g m) where
  empty = Expr empty
  (Expr p) <|> (Expr q) = Expr (p <|> q)

instance Monad m => Monad (Expr nt p g m) where
  return = Expr . return
  fail = Expr . fail
  (Expr p) >> (Expr q) = Expr $ p >> q
  (Expr p) >>= f = Expr $ p >>= unExpr . f

instance MonadPlus m => MonadPlus (Expr nt p g m) where
  mzero = Expr mzero
  (Expr p) `mplus` (Expr q) = Expr (p `mplus` q)

instance MonadIO m => MonadIO (Expr nt p g m) where
  liftIO = Expr . liftIO

instance MonadError SomeException m => MonadError SomeException (Expr nt p g m) where
  throwError = Expr . throwError
  catchError (Expr m) f = Expr $ catchError m (unExpr . f)

instance MonadTrans (Expr nt p g) where
  lift = Expr . lift

instance MonadFail m => MonadFail (Expr nt p g m) where
  fail = lift . F.fail

instance MonadCont m => MonadCont (Expr nt p g m) where
  callCC f
    = Expr
    $ do env <- ask
         lift $ callCC $ \k -> runReaderT (unExpr $ f $ lift . k) env

instance MonadReader r m => MonadReader r (Expr nt p g m) where
  ask    = lift $ ask
  local  = exprLift1 . local

instance MonadWriter w m => MonadWriter w (Expr nt p g m) where
  writer = lift . writer
  tell   = lift . tell
  listen = exprLift1 listen
  pass   = exprLift1 pass

instance MonadState s m => MonadState s (Expr nt p g m) where
  get    = lift $ get
  put    = lift . put
  state  = lift . state

instance MonadRWS r w s m => MonadRWS r w s (Expr nt p g m)

instance MonadFix m => MonadFix (Expr nt p g m) where
  mfix f = Expr $ ask >>= \env -> lift $ mfix $ \(~x) -> runReaderT (unExpr $ f x) env


newtype ExprUnlift nt p g m = ExprUnlift { unlift :: forall b . Expr nt p g m b -> m b }

exprLiftM :: Monad m => (ExprUnlift nt p g m -> m a) -> Expr nt p g m a
exprLiftM f = Expr $ ask >>= \env -> lift $ f $ ExprUnlift $ \(Expr m) -> runReaderT m env

exprLift1 :: Monad m => (m a -> m b) -> Expr nt p g m a -> Expr nt p g m b
exprLift1 f (Expr m) = Expr $ ask >>= lift . f . runReaderT m

instance MonadFlow m => MonadFlow (Expr nt p g m) where
  type Branch (Expr nt p g m) = Branch m
  fork   = exprLift1 fork
  merge  = lift . merge
  loop f = Expr $
    do c <- ask
       lift $ loop $ \x -> runReaderT (unExpr $ f x) c

instance (IsString a, Applicative m) => IsString (Expr nt p g m a) where
  fromString = pure . fromString

instance (Monoid a, Applicative m) => Monoid (Expr nt p g m a) where
  mempty  = pure mempty
  mappend = liftA2 mappend

instance (Semigroup a, Applicative m) => Semigroup (Expr nt p g m a) where
  (<>) = liftA2 (<>)

instance Monad m => MonadZip (Expr nt p g m) where
  mzipWith f p q = f <$> p <*> q

instance (Bounded a, Applicative m) => Bounded (Expr nt p g m a) where
  minBound = pure minBound
  maxBound = pure maxBound

instance (Num a, Applicative m) => Num (Expr nt p g m a) where
  (+)    = liftA2 (+)
  (-)    = liftA2 (-)
  (*)    = liftA2 (*)
  negate = fmap negate
  abs    = fmap abs
  signum = fmap signum
  fromInteger = pure . fromInteger

instance (Fractional a, Applicative m) => Fractional (Expr nt p g m a) where
  (/)   = liftA2 (/)
  recip = fmap recip
  fromRational = pure . fromRational

instance (Floating a, Applicative m) => Floating (Expr nt p g m a) where
  pi      = pure pi
  exp     = fmap exp
  log     = fmap log
  sqrt    = fmap sqrt
  (**)    = liftA2 (**)
  logBase = liftA2 logBase
  sin     = fmap sin
  cos     = fmap cos
  tan     = fmap tan
  asin    = fmap asin
  acos    = fmap acos
  atan    = fmap atan
  sinh    = fmap sinh
  cosh    = fmap cosh
  tanh    = fmap tanh
  asinh   = fmap asinh
  acosh   = fmap acosh
  atanh   = fmap atanh

(∨) :: Applicative m => Expr nt p g m Bool -> Expr nt p g m Bool -> Expr nt p g m Bool
(∨) = liftA2 (||)

(∧) :: Applicative m => Expr nt p g m Bool -> Expr nt p g m Bool -> Expr nt p g m Bool
(∧) = liftA2 (&&)

(≡) :: (Applicative m, Eq a) => Expr nt p g m a -> Expr nt p g m a -> Expr nt p g m Bool
(≡) = liftA2 (==)

(≠) :: (Applicative m, Eq a) => Expr nt p g m a -> Expr nt p g m a -> Expr nt p g m Bool
(≠) = liftA2 (/=)

(¬) :: Applicative m => Expr nt p g m Bool -> Expr nt p g m Bool
(¬) = fmap not

(<≡) :: (Ord a, Applicative m) => Expr nt p g m a -> Expr nt p g m a -> Expr nt p g m Bool
(<≡) = liftA2 (<=)

(>≡) :: (Ord a, Applicative m) => Expr nt p g m a -> Expr nt p g m a -> Expr nt p g m Bool
(>≡) = liftA2 (<=)

(<!) :: (Ord a, Applicative m) => Expr nt p g m a -> Expr nt p g m a -> Expr nt p g m Bool
(<!) = liftA2 (<)

(!>) :: (Ord a, Applicative m) => Expr nt p g m a -> Expr nt p g m a -> Expr nt p g m Bool
(!>) = liftA2 (>)


data SomeExpr m g = SomeExpr (Maybe (Expr Any Any g m Any)) (Maybe (ExprTrans Any Any g m Any Any))

unsafeCoerceExpr :: Expr nt p g m a -> Expr nt' p' g m a'
unsafeCoerceExpr e = unsafeCoerce e

unsafeCoerceTrans :: ExprTrans nt p g m a b -> ExprTrans nt' p' g m a' b'
unsafeCoerceTrans t = unsafeCoerce t

unsafeFromAnyExpr :: Expr nt p g m Any -> Expr nt p g m a
unsafeFromAnyExpr e = unsafeCoerce e

toAnyExpr :: Expr nt p g m a -> Expr nt p g m Any
toAnyExpr e = unsafeCoerce e

mkSomeExpr :: Expr nt p g m a -> SomeExpr m g
mkSomeExpr e = SomeExpr (Just $ unsafeCoerceExpr e) Nothing

mkSomeExprT :: ExprTrans nt p g m a b -> SomeExpr m g
mkSomeExprT t = SomeExpr Nothing (Just $ unsafeCoerceTrans t)

-- A right-biased union is used
unsafeUnionSomeExpr :: SomeExpr m g -> SomeExpr m g -> SomeExpr m g
unsafeUnionSomeExpr (SomeExpr p q) (SomeExpr r s) = SomeExpr (r <|> p) (s <|> q)

unsafeFromSomeExpr :: SomeExpr m g -> Expr nt p g m a
unsafeFromSomeExpr (SomeExpr (Just e) mb) = unsafeCoerceExpr (maybe e ($ e) mb)


--
-- Node resolution
--

data NodeRef
  = LhsNode
  | LocNode
  | ChildNode Symbol

type family ToNodeRef c where
  ToNodeRef "lhs" = 'LhsNode
  ToNodeRef "loc" = 'LocNode
  ToNodeRef c     = 'ChildNode c

type family ResolveNodeRef r m nt p g where
  ResolveNodeRef 'LhsNode       m nt p g = AppBranch m (GetInhAttrs nt g)
  ResolveNodeRef 'LocNode       m nt p g = AppBranchLoc m (GetLocAttrs nt p g)
  ResolveNodeRef ('ChildNode c) m nt p g = AppBranch m (GetChildAttrs nt p c g)

type family AppBranch m t where
  AppBranch m ('D.Bin n s a l r) = 'D.Bin n s (Branch m a) (AppBranch m l) (AppBranch m r)
  AppBranch m 'D.Tip             = 'D.Tip

type family AppBranchLoc m t where
  AppBranchLoc m ('D.Bin n s ('InternalType a _) l r) = 'D.Bin n s (Branch m a) (AppBranchLoc m l) (AppBranchLoc m r)
  AppBranchLoc m 'D.Tip                               = 'D.Tip

class ResolveAttrs (r :: NodeRef) m where
  resolveAttrs :: (ResolveNodeRef r m nt p g ~ t) => Proxy r -> Env m nt p g -> m (D.Rec t)

instance MonadFlow m => ResolveAttrs 'LhsNode m where
  resolveAttrs _ (Env _ _ _ m) = pure $ D.unsafeFromAssocs m

instance MonadFlow m => ResolveAttrs 'LocNode m where
  resolveAttrs _ (Env _ _ m _) = pure $ D.unsafeFromAssocs m

instance (KnownSymbol c, MonadFlow m) => ResolveAttrs ('ChildNode c) m where
  resolveAttrs = resolveChildAttrs Proxy

resolveChildAttrs :: (KnownSymbol c, MonadFlow m, (ResolveNodeRef ('ChildNode c) m nt p g) ~ t) => Proxy c -> Proxy ('ChildNode c) -> Env m nt p g -> m (D.Rec t)
resolveChildAttrs c _ (Env _ cs _ _) = D.unsafeFromAssocs <$> merge (HM.lookupDefault (error "Internal error: child not in environment") (T.pack $ symbolVal c) cs)

type ValidAttrs c m nt p g t = ((ResolveNodeRef (ToNodeRef c) m nt p g) ~ t, ResolveAttrs (ToNodeRef c) m)

attrs :: (MonadFlow m, ValidAttrs c m nt p g t) => Proxy c -> Expr nt p g m (D.Rec (D.Normalize t))
attrs c
  = Expr
  $ do e <- ask
       lift $ D.normalize <$> resolveAttrs (toRef c) e
  where
    toRef :: Proxy c -> Proxy (ToNodeRef c)
    toRef _ = Proxy


type family ResolveAttrRef r nt p attr g where
  ResolveAttrRef 'LhsNode       nt p attr g = ResolveAttrRef_Lhs   (D.Lookup attr (GetInhAttrs nt g))         attr
  ResolveAttrRef 'LocNode       nt p attr g = ResolveAttrRef_Loc   (D.Lookup attr (GetLocAttrs nt p g))       attr
  ResolveAttrRef ('ChildNode c) nt p attr g = ResolveAttrRef_Child (D.Lookup attr (GetChildAttrs nt p c g)) c attr

type family ResolveAttrRef_Lhs mb attr where
  ResolveAttrRef_Lhs (Just a) _    = a
  ResolveAttrRef_Lhs 'Nothing attr = TypeError ('Text "Undeclared inherited attribute: " :<>: ShowType attr)

type family ResolveAttrRef_Loc mb attr where
  ResolveAttrRef_Loc (Just ('InternalType a _)) _    = a
  ResolveAttrRef_Loc 'Nothing                   attr = TypeError ('Text "Undeclared local attribute: " :<>: ShowType attr)

type family ResolveAttrRef_Child mb c attr where
  ResolveAttrRef_Child (Just a) _ _    = a
  ResolveAttrRef_Child 'Nothing c attr = TypeError ('Text "Undeclared synthesized attribute: " :<>: ShowType c :<>: ShowType "." :<>: ShowType attr)

class ResolveAttr (r :: NodeRef) where
  resolveAttr :: (MonadFlow m, KnownSymbol attr, ResolveAttrRef r nt p attr g ~ a) => Proxy r -> Proxy attr -> Expr nt p g m (Branch m a)

instance ResolveAttr 'LhsNode where
  resolveAttr _ attr = unsafeResolveAttr attr (\(Env _ _ _ lhs) -> pure lhs)

instance ResolveAttr 'LocNode where
  resolveAttr _ attr = unsafeResolveAttr attr (\(Env _ _ locs _) -> pure locs)

instance KnownSymbol c => ResolveAttr ('ChildNode c) where
  resolveAttr c attr
    = unsafeResolveAttr attr f
    where
      f (Env _ cs _ _) = merge (HM.lookupDefault (error "Internal error") childname cs)
      childname = T.pack $ symbolVal (mkCP c)

      mkCP :: Proxy ('ChildNode c) -> Proxy c
      mkCP _ = Proxy

unsafeResolveAttr :: (MonadFlow m, KnownSymbol attr) => Proxy attr -> (Env m nt p g -> m (AttrMap m)) -> Expr nt p g m (Branch m a)
unsafeResolveAttr attr f
  = Expr
  $ do e <- ask
       lift $ f e >>= unsafeResolveAttr' attr

unsafeResolveAttr' :: (MonadFlow m, KnownSymbol attr) => Proxy attr -> AttrMap m -> m (Branch m a)
unsafeResolveAttr' attr mp
  = unsafeFromAnyBranch $ HM.lookupDefault (error "Internal error") attrname mp
  where
    attrname = T.pack $ symbolVal attr

type ValidAttrRef nt p c attr g a
  = (KnownSymbol attr, ResolveAttrRef (ToNodeRef c) nt p attr g ~ a, ResolveAttr (ToNodeRef c) )

getAttr :: (MonadFlow m, ValidAttrRef nt p c attr g a) => Proxy c -> Proxy attr -> Expr nt p g m (Branch m a)
getAttr c attr = resolveAttr (mkCP c) attr where
  mkCP :: Proxy c -> Proxy (ToNodeRef c)
  mkCP _ = Proxy

(!) :: (MonadFlow m, ValidAttrRef nt p c attr g a) => Proxy c -> Proxy attr -> Expr nt p g m a
c ! attr
  = case getAttr c attr of
        Expr m -> Expr $ m >>= lift . merge

infixl 9 !


--
-- Combinators for building grammar values
--

type BranchMap m t = HashMap Text (Branch m t)
type AttrMap m = BranchMap m Any

data Env (m :: Type -> Type) (nt :: Symbol) (p :: Symbol) (g :: Grammar)
  = Env Any (BranchMap m (AttrMap m)) (AttrMap m) (AttrMap m)

data ProdCon (m :: Type -> Type) (nt :: Symbol) = ProdCon Text Any ((AttrMap m -> m (AttrMap m)) -> AttrMap m -> m (AttrMap m))

newtype Module (m :: Type -> Type) (g :: Grammar) (ds :: Decls)
  = Module (HashMap Text (Rules m g))

type Rules m g = HashMap RuleId (SomeExpr m g)

unsafeFromAnyBranch :: Monad m => Branch m Any -> m (Branch m a)
unsafeFromAnyBranch x = pure $ unsafeCoerce x

prodKey :: (KnownSymbol nt, KnownSymbol prod) => Proxy nt -> Proxy prod -> Text
prodKey nt prod = prodKey' nt (T.pack $ symbolVal prod)

prodKey' :: KnownSymbol nt => Proxy nt -> Text -> Text
prodKey' nt prod = (T.pack $ symbolVal nt) <> T.singleton '.' <> prod

emptyModule :: Proxy m -> Module m g 'EmptyDecls
emptyModule _ = Module HM.empty

declNont :: KnownSymbol nt => Proxy nt -> Module m g ('SingleDecl ('NontDecl nt))
declNont Proxy = Module HM.empty

declProd :: (MonadFlow m, KnownSymbol nt, KnownSymbol prod, CompleteProd nt prod g) => Proxy nt -> Proxy prod -> Proxy ty -> Module m g ('SingleDecl ('ProdDecl nt prod ty))
declProd nt prod ty = initProdWithAutoRules nt prod ty Proxy

declInh :: (KnownSymbol nt, KnownSymbol attr) => Proxy nt -> Proxy attr -> Proxy ty -> Module m g ('SingleDecl ('InhDecl nt attr ty))
declInh Proxy Proxy Proxy = Module HM.empty

declSyn :: (KnownSymbol nt, KnownSymbol attr) => Proxy nt -> Proxy attr -> Proxy ty -> Module m g ('SingleDecl ('SynDecl nt attr ty))
declSyn Proxy Proxy Proxy = Module HM.empty

defChild :: (MonadFlow m, KnownSymbol nt, KnownSymbol prod, KnownSymbol child, KnownSymbol childNt, CompleteChild nt prod child g) =>
  Proxy nt -> Proxy prod -> Proxy child -> Proxy childNt -> Expr nt prod g m (ProdCon m childNt) -> Module m g ('SingleDecl ('ChildDef nt prod child childNt))
defChild nt prod child nt' e = Module $ HM.singleton (prodKey nt prod) $ HM.fromList $ (childRuleKey child, mkSomeExpr e) : augmentChild nt prod child e

redefChild :: (KnownSymbol nt, KnownSymbol prod, KnownSymbol child, ValidChildType g nt prod child childNt) =>
  Proxy nt -> Proxy prod -> Proxy child -> ExprTrans nt prod g m (ProdCon m childNt) (ProdCon m childNt) -> Module m g ('SingleDecl ('ChildReDef nt prod child))
redefChild nt prod child e = Module $ HM.singleton (prodKey nt prod) $ HM.singleton (childRuleKey child) $ mkSomeExprT e

defInh :: (KnownSymbol nt, KnownSymbol prod, KnownSymbol child, KnownSymbol attr, ValidChildInhType 'False g nt prod child attr a a) =>
  Proxy nt -> Proxy prod -> Proxy child -> Proxy attr -> Expr nt prod g m a -> Module m g ('SingleDecl ('InhDef nt prod child attr a))
defInh nt prod child attr e = Module $ HM.singleton (prodKey nt prod) $ HM.singleton (inhRuleKey child attr) $ mkSomeExpr e

redefInh :: (KnownSymbol nt, KnownSymbol prod, KnownSymbol child, KnownSymbol attr, ValidChildInhType 'True g nt prod child attr a b) =>
  Proxy nt -> Proxy prod -> Proxy child -> Proxy attr -> ExprTrans nt prod g m a b -> Module m g ('SingleDecl ('InhReDef nt prod child attr b))
redefInh nt prod child attr e = Module $ HM.singleton (prodKey nt prod) $ HM.singleton (inhRuleKey child attr) $ mkSomeExprT e

defLoc :: (KnownSymbol nt, KnownSymbol prod, KnownSymbol attr, ValidLocType 'False g nt prod attr a a) =>
  Proxy nt -> Proxy prod -> Proxy attr -> Expr nt prod g m a -> Module m g ('SingleDecl ('LocDef nt prod attr a))
defLoc nt prod attr e = Module $ HM.singleton (prodKey nt prod) $ HM.singleton (locRuleKey attr) $ mkSomeExpr e

redefLoc :: (KnownSymbol nt, KnownSymbol prod, KnownSymbol attr, ValidLocType 'True g nt prod attr a b) =>
  Proxy nt -> Proxy prod -> Proxy attr -> ExprTrans nt prod g m a b -> Module m g ('SingleDecl ('LocReDef nt prod attr b))
redefLoc nt prod attr e = Module $ HM.singleton (prodKey nt prod) $ HM.singleton (locRuleKey attr) $ mkSomeExprT e

defLhs :: (KnownSymbol nt, KnownSymbol prod, KnownSymbol attr, ValidLhsSynType 'False g nt prod attr a a) =>
  Proxy nt -> Proxy prod -> Proxy attr -> Expr nt prod g m a -> Module m g ('SingleDecl ('LhsDef nt prod attr a))
defLhs nt prod attr e = Module $ HM.singleton (prodKey nt prod) $ HM.singleton (lhsRuleKey attr) $ mkSomeExpr e

redefLhs :: (KnownSymbol nt, KnownSymbol prod, KnownSymbol attr, ValidLhsSynType 'True g nt prod attr a b) =>
  Proxy nt -> Proxy prod -> Proxy attr -> ExprTrans nt prod g m a b -> Module m g ('SingleDecl ('LhsReDef nt prod attr b))
redefLhs nt prod attr e = Module $ HM.singleton (prodKey nt prod) $ HM.singleton (lhsRuleKey attr) $ mkSomeExprT e

prod :: (Monad m, KnownSymbol nt, KnownSymbol prod, ValidProdRef nt prod g a) => Proxy nt -> Proxy prod -> a -> Expr nt' prod' g m (ProdCon m nt)
prod _ prod a = Expr $ return $ ProdCon (T.pack $ symbolVal prod) (unsafeCoerce a) ($)

aroundChild :: (Monad m, (AppBranch m (D.Normalize (GetInhAttrs nt g)) ~ i), (AppBranch m (D.Normalize (GetSynAttrs nt g))) ~ s) =>
  ((D.Rec i -> m (D.Rec s)) -> D.Rec i -> m (D.Rec s)) -> Expr nt' prod' g m (ProdCon m nt) -> Expr nt' prod' g m (ProdCon m nt)
aroundChild f1 (Expr e) = Expr $ do
  (ProdCon k v f0) <- e
  return $ ProdCon k v $ \f -> (unsafeCoerce f1) (f0 f)

this :: Monad m => Expr nt prod g m (GetProdType nt prod g)
this = Expr $ do
  Env val _ _ _ <- ask
  return $ unsafeCoerce val

reflChildren :: Monad m => Expr nt prod g m (Proxy (GetChildren nt prod g))
reflChildren = pure Proxy

(§§) :: Module m g a -> Module m g b -> Module m g ('ComposeDecls a b)
Module p §§ Module q = Module (mergeDecls p q)

infixr 0 §§

mergeDecls :: HashMap Text (HashMap RuleId (SomeExpr m g)) -> HashMap Text (HashMap RuleId (SomeExpr m g)) -> HashMap Text (HashMap RuleId (SomeExpr m g))
mergeDecls = HM.unionWith (HM.unionWith unsafeUnionSomeExpr)


--
-- Syntactic sugar
--

data RulePatType
  = AttrPat  Symbol Symbol
  | ChildPat Symbol Symbol
  | AliasPat Symbol AliasPatType

data AliasPatType
  = PairPat RulePatType RulePatType

data RulePat (redef :: Bool) (nt :: Symbol) (p :: Symbol) (m :: Type -> Type) (g :: Grammar) (t :: RulePatType) (a :: Type) (b :: Type) where
  DefAttr  :: (KnownSymbol c, KnownSymbol attr, ToNodeRefSing (ToNodeRef c), AttrPatCtx redef (ToNodeRef c) attr nt p g a b) => RulePat redef nt p m g ('AttrPat c attr) a b
  DefChild :: (MonadFlow m, KnownSymbol c, KnownSymbol nt', a ~ ProdCon m nt', ChildPatCtx redef c nt p nt' g) => RulePat redef nt p m g ('ChildPat c nt') a a
  DefAlias :: (KnownSymbol attr, ValidLocType redef g nt p attr a b) => AliasPat redef nt p m g t a b -> RulePat redef nt p m g ('AliasPat attr t) a b

data AliasPat (redef :: Bool) (nt :: Symbol) (p :: Symbol) (m :: Type -> Type) (g :: Grammar) (t :: AliasPatType) (a :: Type) (b :: Type) where
  (:*:) :: RulePat redef nt p m g l s u -> RulePat redef nt p m g r t v -> AliasPat redef nt p m g ('PairPat l r) (s, t) (u, v)

(?) :: (KnownSymbol c, KnownSymbol attr, ToNodeRefSing (ToNodeRef c), AttrPatCtx redef (ToNodeRef c) attr nt p g a b) => Proxy c -> Proxy attr -> RulePat redef nt p m g ('AttrPat c attr) a b
(?) _ _ = DefAttr

(?:) :: (MonadFlow m, KnownSymbol c, KnownSymbol nt', a ~ ProdCon m nt', ChildPatCtx redef c nt p nt' g) => Proxy c -> Proxy nt' -> RulePat redef nt p m g ('ChildPat c nt') a a
(?:) _ _ = DefChild

(@?) :: (KnownSymbol attr, ValidLocType redef g nt p attr a b) => Proxy attr -> AliasPat redef nt p m g t a b -> RulePat redef nt p m g ('AliasPat attr t) a b
(@?) _ = DefAlias

infix 8 ?
infix 8 ?:
infix 6 @?
infix 7 :*:

data RuleDefs (m :: Type -> Type) (nt :: Symbol) (p :: Symbol) (g :: Grammar) (ds :: Decls) where
  EmptyRuleDefs :: RuleDefs m nt p g 'EmptyDecls
  (:=) :: (KnownSymbol nt, KnownSymbol p, ds ~ RulePatDecls 'False pat nt p a) => RulePat 'False nt p m g pat a a -> Expr nt p g m a -> RuleDefs m nt p g ds
  (:+) :: (KnownSymbol nt, KnownSymbol p, ds ~ RulePatDecls 'True pat nt p b)  => RulePat 'True nt p m g pat a b -> ExprTrans nt p g m a b -> RuleDefs m nt p g ds
  (:§) :: RuleDefs m nt p g a -> RuleDefs m nt p g b -> RuleDefs m nt p g ('ComposeDecls a b)

infix 4 :=
infix 4 :+
infix 4 :§

type family AttrPatCtx redef r attr nt p g a b :: Constraint where
  AttrPatCtx redef  'LhsNode       attr nt p g a b = (ValidLhsSynType redef g nt p attr a b)
  AttrPatCtx redef  'LocNode       attr nt p g a b = (ValidLocType redef g nt p attr a b)
  AttrPatCtx redef  ('ChildNode c) attr nt p g a b = (KnownSymbol c, ValidChildInhType redef g nt p c attr a b)

type family ChildPatCtx redef c nt p nt' g :: Constraint where
  ChildPatCtx 'False c nt p nt' g = CompleteChild nt p c g
  ChildPatCtx 'True  c nt p nt' g = ValidChildType g nt p c nt'

type family RulePatDecls (redef :: Bool) (pat :: RulePatType) (nt :: Symbol) (p :: Symbol) (a :: Type) :: Decls where
  RulePatDecls 'False ('AttrPat c attr) nt p a
    = 'SingleDecl (RulePatDecls1 (ToNodeRef c) attr nt p a)
  RulePatDecls 'False ('ChildPat c nt') nt p _
    = 'SingleDecl ('ChildDef nt p c nt')
  RulePatDecls 'True ('AttrPat c attr) nt p a
    = 'SingleDecl (RulePatDecls2 (ToNodeRef c) attr nt p a)
  RulePatDecls 'True ('ChildPat c _) nt p _
    = 'SingleDecl ('ChildReDef nt p c)
  RulePatDecls 'False ('AliasPat attr pt) nt p a
    = RulePatDecls3 attr pt nt p a
  RulePatDecls 'True ('AliasPat attr pt) nt p a
      = RulePatDecls4 attr pt nt p a

type family RulePatDecls1 r attr nt p a :: Decl where
  RulePatDecls1 'LhsNode       attr nt p a = 'LhsDef nt p attr a
  RulePatDecls1 'LocNode       attr nt p a = 'LocDef nt p attr a
  RulePatDecls1 ('ChildNode c) attr nt p a = 'InhDef nt p c attr a

type family RulePatDecls2 r attr nt p a :: Decl where
  RulePatDecls2 'LhsNode       attr nt p a = 'LhsReDef nt p attr a
  RulePatDecls2 'LocNode       attr nt p a = 'LocReDef nt p attr a
  RulePatDecls2 ('ChildNode c) attr nt p a = 'InhReDef nt p c attr a

type family RulePatDecls3 attr pt nt p a :: Decls where
  RulePatDecls3 attr ('PairPat l r) nt p a
    = 'ComposeDecls ('SingleDecl ('LocDef nt p attr a))
        ('ComposeDecls (RulePatDecls 'False l nt p (PairFst a)) (RulePatDecls 'False r nt p (PairSnd a)))

type family RulePatDecls4 attr pt nt p a :: Decls where
  RulePatDecls4 attr ('PairPat l r) nt p a = 'SingleDecl ('LocReDef nt p attr a)


type family PairFst (pair :: Type) where
  PairFst (a, _) = a
  PairFst t      = TypeError ('Text "Expecting a pair, not " :<>: ShowType t)

type family PairSnd (pair :: Type) where
  PairSnd (_, b) = b
  PairSnd t      = TypeError ('Text "Expecting a pair, not " :<>: ShowType t)


data AttrDefs (m :: Type -> Type) (nts :: [Symbol]) (g :: Grammar) (ds :: Decls) where
  EmptyAttrDefs :: AttrDefs m nts g 'EmptyDecls
  AttrDef :: AttrDef nts decls -> AttrDefs m nts g decls
  (:§§)   :: AttrDefs m nts g a -> AttrDefs m nts g b -> AttrDefs m nts g ('ComposeDecls a b)
  (:::)   :: AttrDefs m nts g decls -> Proxy ty -> AttrDefs m nts g (InjectType decls ty)

infix 4 :§§
infix 6 :::

data AttrDef (nts :: [Symbol]) (t :: Decls) where
  AttrInh :: KnownSymbol attr => Proxy attr -> AttrDef nts (MkInhDecls nts attr ty)
  AttrSyn :: KnownSymbol attr => Proxy attr -> AttrDef nts (MkSynDecls nts attr ty)

type family InjectType (decls :: Decls) ty where
  InjectType ('SingleDecl decl)  ty = 'SingleDecl (InjectType' decl ty)
  InjectType ('ComposeDecls p q) ty = 'ComposeDecls (InjectType p ty) (InjectType q ty)
  InjectType 'EmptyDecls         ty = 'EmptyDecls

type family InjectType' decl ty where
  InjectType' ('InhDecl nt attr _) ty = 'InhDecl nt attr ty
  InjectType' ('SynDecl nt attr _) ty = 'SynDecl nt attr ty

type family MkInhDecls nts attr ty = r | r -> nts attr ty where
  MkInhDecls '[nt]       attr ty = 'SingleDecl ('InhDecl nt attr ty)
  MkInhDecls (nt ': nts) attr ty = 'ComposeDecls ('SingleDecl ('InhDecl nt attr ty)) (MkInhDecls nts attr ty)

type family MkSynDecls nts attr ty = r | r -> nts attr ty where
  MkSynDecls '[nt]       attr ty = 'SingleDecl ('SynDecl nt attr ty)
  MkSynDecls (nt ': nts) attr ty = 'ComposeDecls ('SingleDecl ('SynDecl nt attr ty)) (MkSynDecls nts attr ty)

inh :: KnownSymbol attr => Proxy attr -> AttrDefs m nts g (MkInhDecls nts attr ty)
inh = AttrDef . AttrInh

syn :: KnownSymbol attr => Proxy attr -> AttrDefs m nts g (MkSynDecls nts attr ty)
syn = AttrDef . AttrSyn


rules :: (MonadFlow m, KnownSymbol nt, KnownSymbol p, CompleteProd nt p g) => Proxy nt -> Proxy p -> RulesStart m nt p g 'EmptyDecls
rules _ _ = RulesStart

attributes :: KnownSymbol nt => Proxy nt -> AttrsStart m '[nt] g 'EmptyDecls
attributes _ = AttrsStart

data RulesStart (m :: Type -> Type) (nt :: Symbol) (p :: Symbol) (g :: Grammar) (ds :: Decls) where
  RulesStart :: (MonadFlow m, KnownSymbol nt, KnownSymbol p) => RulesStart m nt p g 'EmptyDecls

data AttrsStart (m :: Type -> Type) (nts :: [Symbol]) (g :: Grammar) (ds :: Decls) where
  AttrsStart :: KnownSymbol nt => AttrsStart m '[nt] g 'EmptyDecls
  AttrsCons  :: KnownSymbol nt => AttrsStart m nts g decls ->
    AttrsStart m (nt ': nts) g decls

data ComposeType = ComposeRules Symbol Symbol | ComposeAttrs [Symbol]

data ComposeState = Start | More

type family ComposeLhs m g t s ds = r | r -> m g t s ds where
  ComposeLhs m g ('ComposeRules nt p) 'Start ds = RulesStart m nt p g ds
  ComposeLhs m g ('ComposeRules nt p) 'More  ds = RuleDefs m nt p g ds
  ComposeLhs m g ('ComposeAttrs nts)  'Start ds = AttrsStart m nts g ds
  ComposeLhs m g ('ComposeAttrs nts)  'More  ds = AttrDefs m nts g ds

type family ComposeRhs m g t ds = r | r -> m g t ds where
  ComposeRhs m g ('ComposeRules nt p) ds = RuleDefs m nt p g ds
  ComposeRhs m g ('ComposeAttrs nts)  ds = AttrDefs m nts g ds

type family ComposeRes m g t s ds = r | r -> m g s ds where
  ComposeRes m g ('ComposeRules _ _)  'Start ds = Module m g ds
  ComposeRes m g ('ComposeRules nt p) 'More  ds = RuleDefs m nt p g ds
  ComposeRes m g ('ComposeAttrs _)    'Start ds = Module m g ds
  ComposeRes m g ('ComposeAttrs nts)  'More  ds = AttrDefs m nts g ds

class HasCompose (t :: ComposeType) (s :: ComposeState) where
  (§) :: ComposeLhs m g t s a -> ComposeRhs m g t b -> ComposeRes m g t s ('ComposeDecls a b)

infixr 1 §

instance HasCompose ('ComposeRules nt p) 'Start where
  s@RulesStart § defs = rules' (mkNtP s) (mkProdP s) (EmptyRuleDefs :§ defs) where
    mkNtP :: RulesStart m nt p g ds -> Proxy nt
    mkNtP _ = Proxy

    mkProdP :: RulesStart m nt p g ds -> Proxy p
    mkProdP _ = Proxy

instance HasCompose ('ComposeRules nt p) 'More where
  (§) = (:§)

instance HasCompose ('ComposeAttrs nts) 'Start where
  s § defs = attributes' (mkEmptyAttrDefs s :§§ defs)

mkEmptyAttrDefs :: AttrsStart m nts g ds -> AttrDefs m nts g ds
mkEmptyAttrDefs AttrsStart = EmptyAttrDefs
mkEmptyAttrDefs (AttrsCons s) =
  case mkEmptyAttrDefs s of
    EmptyAttrDefs -> EmptyAttrDefs

instance HasCompose ('ComposeAttrs nts) 'More where
  (§) = (:§§)

rules' :: (MonadFlow m, KnownSymbol nt, KnownSymbol p) => Proxy nt -> Proxy p -> RuleDefs m nt p g ds -> Module m g ds
rules' _ _  EmptyRuleDefs = emptyModule Proxy
rules' nt p (a :§ b)      = rules' nt p a §§ rules' nt p b
rules' nt p (pat := e)
  = case pat of
      DefAttr  ->
        let singRef = toNodeRefSing (mkAttrCP pat)
            attr    = (mkAttrNameP pat)
        in case singRef of
             NodeRefLhs     -> defLhs nt p attr e
             NodeRefLoc     -> defLoc nt p attr e
             NodeRefChild c -> defInh nt p c attr e
      DefChild -> defChild nt p (mkChildCP pat) (mkChildNtP pat) e
      DefAlias (l :*: r) ->
        let locname = mkLocNameP pat
            fetch = unsafeFromAnyExpr $ Expr
                  $ do (Env _ _ locs _) <- ask
                       lift $ merge $ HM.lookupDefault (error "Internal error") (T.pack $ symbolVal $ locname) locs
        in defLoc nt p locname e
           §§ rules' nt p (l := (fst <$> fetch))
           §§ rules' nt p (r := (snd <$> fetch))
rules' nt p (pat :+ f)
  = case pat of
      DefAttr  ->
        let singRef = toNodeRefSing (mkAttrCP pat)
            attr    = (mkAttrNameP pat)
        in case singRef of
             NodeRefLhs     -> redefLhs nt p attr f
             NodeRefLoc     -> redefLoc nt p attr f
             NodeRefChild c -> redefInh nt p c attr f
      DefChild           -> redefChild nt p (mkChildCP pat) f
      DefAlias (_ :*: _) -> redefLoc nt p (mkLocNameP pat) f

mkAttrCP :: RulePat redef nt p m g ('AttrPat c attr) a b -> Proxy (ToNodeRef c)
mkAttrCP _ = Proxy

mkAttrNameP :: RulePat redef nt p m g ('AttrPat c attr) a b -> Proxy attr
mkAttrNameP _ = Proxy

mkChildCP :: RulePat redef nt p m g ('ChildPat c nt') a b -> Proxy c
mkChildCP _ = Proxy

mkChildNtP :: RulePat redef nt p m g ('ChildPat c nt') a b -> Proxy nt'
mkChildNtP _ = Proxy

mkLocNameP :: RulePat redef nt p m g ('AliasPat attr pt) a b -> Proxy attr
mkLocNameP _ = Proxy

data NodeRefSing (r :: NodeRef) where
  NodeRefLhs   :: NodeRefSing 'LhsNode
  NodeRefLoc   :: NodeRefSing 'LocNode
  NodeRefChild :: Proxy c -> NodeRefSing ('ChildNode c)

class ToNodeRefSing (r :: NodeRef) where
  toNodeRefSing :: Proxy r -> NodeRefSing r

instance ToNodeRefSing 'LhsNode where
  toNodeRefSing _ = NodeRefLhs

instance ToNodeRefSing 'LocNode where
  toNodeRefSing _ = NodeRefLoc

instance ToNodeRefSing ('ChildNode c) where
  toNodeRefSing p = NodeRefChild (mkP p) where
    mkP :: Proxy ('ChildNode c) -> Proxy c
    mkP _ = Proxy

attributes' :: AttrDefs m nts g ds -> Module m g ds
attributes' _ = Module HM.empty

(&:) :: KnownSymbol nt => AttrsStart m nts g 'EmptyDecls -> Proxy nt ->
  AttrsStart m (nt ': nts) g 'EmptyDecls
s &: _ = AttrsCons s

infixl 8 &:


productions :: KnownSymbol nt => Proxy nt -> Module m g ('SingleDecl ('NontDecl nt))
productions = declNont

type family ExtractNtDecl t where
  ExtractNtDecl ('SingleDecl ('NontDecl nt)) = nt
  ExtractNtDecl ('ComposeDecls a _)          = ExtractNtDecl a

(&|) :: (MonadFlow m, KnownSymbol nt, KnownSymbol p, CompleteProd nt p g, ExtractNtDecl t ~ nt) => Module m g t -> Proxy p -> Module m g ('ComposeDecls t ('SingleDecl ('ProdDecl nt p ty)))
(&|) m p = m §§ declProd Proxy p Proxy

infixl 8 &|


--
-- Assemble
--

newtype Assembly (m :: Type -> Type) (g :: Grammar) (init :: Grammar) = Assembly (HashMap Text (Rules m g))

assemble :: Module m g ds -> Assembly m g (Compile ds EmptyGrammar)
assemble (Module m) = Assembly m

assembleWith :: Module m g' ds -> Assembly m g' g -> Assembly m g' (Compile ds g)
assembleWith (Module p) (Assembly q) = Assembly (mergeDecls p q)


--
-- Auto rule inference
--

-- Note: Types like Map or Set are only monoids when their elements are. We are somewhat optimistic here.
type family AllowedSynMonoids (a :: Type) :: Bool where
  AllowedSynMonoids (Map _ _)         = 'True
  AllowedSynMonoids (Set _)           = 'True
  AllowedSynMonoids (IntMap _)        = 'True
  AllowedSynMonoids (Seq _)           = 'True
  AllowedSynMonoids (HashMap _ _)     = 'True
  AllowedSynMonoids (Product _)       = 'True
  AllowedSynMonoids (Sum _)           = 'True
  AllowedSynMonoids (Max _)           = 'True
  AllowedSynMonoids (Min _)           = 'True
  AllowedSynMonoids SG.Any            = 'True
  AllowedSynMonoids All               = 'True
  AllowedSynMonoids (First _)         = 'True
  AllowedSynMonoids (Last _)          = 'True
  AllowedSynMonoids Text              = 'True
  AllowedSynMonoids [_]               = 'True
  AllowedSynMonoids (WrappedMonoid _) = 'True
  AllowedSynMonoids _                 = 'False

data ExprCtx = CtxLoc | CtxSyn (Dict Child) (Dict InternalType) | CtxInh (Dict InternalType) (Dict Type)

data AutoInhChild    = LocInhChild | LhsInhChild
data AutoSynChildren = LocSynChild Type | OneSynChild Symbol Type | SynChildren [(Symbol, Type)]
data ExprCategory    = ExprGiven | ExprAutoInh AutoInhChild Type | ExprAutoSyn AutoSynChildren | ExprMissing

type GetExprCategory (x :: Symbol) (a :: Type) (defs :: Dict any) (ctx :: ExprCtx) (g :: Grammar)
  = GetExprCategory1 (D.Member x defs) x a ctx g

type family GetExprCategory1 exists x a ctx g where
  GetExprCategory1 'True  _ _ _                   _ = 'ExprGiven
  GetExprCategory1 'False x _ 'CtxLoc             _ = 'ExprMissing
  GetExprCategory1 'False x a ('CtxSyn cs locs)   g = GetExprCategory_Syn (D.Lookup x locs) (GetAttrChildren x (D.Assocs cs) g) (AllowedSynMonoids a)
  GetExprCategory1 'False x _ ('CtxInh locs inhs) _ = GetExprCategory_Inh (D.Lookup x locs) (D.Lookup x inhs)

type family GetExprCategory_Inh mbLoc mbInh where
  GetExprCategory_Inh ('Just ('InternalType ty _)) _ = 'ExprAutoInh 'LocInhChild ty
  GetExprCategory_Inh _ ('Just ty) = 'ExprAutoInh 'LhsInhChild ty
  GetExprCategory_Inh _ _          = 'ExprMissing

type family GetAttrChildren x cs g where
  GetAttrChildren x '[]                       _ = '[]
  GetAttrChildren x ('(c, 'Child nt _) ': cs) g = GetAttrChildren1 (D.Lookup x (GetSynAttrs nt g)) c cs x g

type family GetAttrChildren1 mbTy c cs x g where
  GetAttrChildren1 'Nothing   _ cs x g = GetAttrChildren x cs g
  GetAttrChildren1 ('Just ty) c cs x g = '(c, ty) ': GetAttrChildren x cs g

type family GetExprCategory_Syn mbLoc cs allowed where
  GetExprCategory_Syn ('Just ('InternalType ty _)) _  _     = 'ExprAutoSyn ('LocSynChild ty)
  GetExprCategory_Syn _ '[ '(c, a)] _     = 'ExprAutoSyn ('OneSynChild c a)
  GetExprCategory_Syn _ cs          'True = 'ExprAutoSyn ('SynChildren cs)
  GetExprCategory_Syn _ _           _     = 'ExprMissing


class BuildAutoExpr (d :: ExprCategory) (a :: Type) where
  buildAutoExpr :: MonadFlow m => Proxy '(d, a, m, g) -> RuleId -> SomeExpr m g

instance (a ~ a') => BuildAutoExpr ('ExprAutoInh 'LocInhChild a') a where
  buildAutoExpr _ (InhRuleId _ attr) = mkCopyExpr attr $ \(Env _ _ locs _ ) -> locs

instance (a ~ a') => BuildAutoExpr ('ExprAutoInh 'LhsInhChild a') a where
  buildAutoExpr _ (InhRuleId _ attr) = mkCopyExpr attr $ \(Env _ _ _ syns) -> syns

mkCopyExpr :: MonadFlow m => Text -> (Env m nt p g -> AttrMap m) -> SomeExpr m g
mkCopyExpr attr extract = mkSomeExpr $ Expr $ do
  mp <- asks extract
  lift $ merge $ HM.lookupDefault (error $ "Internal error: rule not implemented: " ++ show attr) attr mp

instance (a ~ a') => BuildAutoExpr ('ExprAutoSyn ('LocSynChild a')) a where
  buildAutoExpr _ (LhsRuleId attr) = mkCopyExpr attr $ \(Env _ _ locs _ ) -> locs

instance (a ~ a', KnownSymbol c) => BuildAutoExpr ('ExprAutoSyn ('OneSynChild c a')) a where
  buildAutoExpr p (LhsRuleId attr)
    = mkSomeExpr
    $ do (Env _ cs _ _) <- Expr ask
         unsafeFromAnyExpr $ merge (cs HM.! childname) >>= \attrs -> merge (attrs HM.! attr)
    where
      childname = T.pack $ symbolVal $ mkCP p

      mkCP :: Proxy '( 'ExprAutoSyn ('OneSynChild c a'), a, m, g) -> Proxy c
      mkCP _ = Proxy

instance (Monoid a, BuildCopyExprs cs a) => BuildAutoExpr ('ExprAutoSyn ('SynChildren cs )) a where
  buildAutoExpr p (LhsRuleId attr)
    = mkSomeExpr
    $ do env <- Expr ask
         mconcat $ buildCopyExprs (mkChildrenP p) (mkTypeP p) attr env
    where
      mkChildrenP :: Proxy '( 'ExprAutoSyn ('SynChildren cs), a, m, g) -> Proxy cs
      mkChildrenP _ = Proxy

      mkTypeP :: Proxy '( 'ExprAutoSyn ('SynChildren cs), a, m, g) -> Proxy a
      mkTypeP _ = Proxy

class BuildCopyExprs (cs :: [(Symbol, Type)]) (a :: Type) where
  buildCopyExprs :: MonadFlow m => Proxy cs -> Proxy a -> Text -> Env m nt p g -> [Expr nt p g m a]

instance BuildCopyExprs '[] a where
  buildCopyExprs _ _ _ _ = []

instance (a ~ a', KnownSymbol c, BuildCopyExprs cs a) => BuildCopyExprs ('(c, a') ': cs) a where
  buildCopyExprs pCs pA attrname env@(Env _ cs _ _)
    = unsafeFromAnyExpr expr : buildCopyExprs (mkTailP pCs) pA attrname env
    where
      expr = merge (cs HM.! childname) >>= \attrs -> merge (attrs HM.! attrname)
      childname = T.pack $ symbolVal $ mkFstP $ mkHeadP pCs


class MkAutoRules (rs :: [(Symbol, ExprCategory, Type)]) where
  mkAutoRules :: MonadFlow m => Proxy '(rs, m, g) -> (Text -> RuleId) -> [(RuleId, SomeExpr m g)]

instance MkAutoRules '[] where
  mkAutoRules _ _ = []

instance (KnownSymbol x, BuildAutoExpr r a, MkAutoRules xs) => MkAutoRules ('(x, r, a) ': xs) where
  mkAutoRules p mkRuleId = (ruleId, buildAutoExpr (mkExprP p) ruleId) : mkAutoRules (mkNextP p) mkRuleId where
    attrname = T.pack $ symbolVal (mkNameP p)
    ruleId   = mkRuleId attrname

    mkNameP :: Proxy '( '(x, r, a) ': xs, m, g) -> Proxy x
    mkNameP _ = Proxy

    mkNextP :: Proxy '( '(x, r, a) ': xs, m, g) -> Proxy '(xs, m, g)
    mkNextP _ = Proxy

    mkExprP :: Proxy '( '(x, r, a) ': xs, m, g) -> Proxy '(r, a, m, g)
    mkExprP _ = Proxy


type family GetAutoRules (attrs :: [(Symbol, Type)]) (defs :: Dict any) (ctx :: ExprCtx) (g :: Grammar) (msg :: ErrorMessage) where
  GetAutoRules '[] defs ctx g msg = '[]
  GetAutoRules ('(x, a) ': xs) defs ctx g msg = GetAutoRules1 (GetExprCategory x a defs ctx g) x a defs ctx g msg xs

type family GetAutoRules1 cat x a defs ctx g msg xs where
  GetAutoRules1 ExprGiven   _ _ defs ctx g msg xs = GetAutoRules xs defs ctx g msg
  GetAutoRules1 ExprMissing x a defs ctx g msg xs = TypeError (msg :<>: 'Text ": attribute " :<>: ShowType x :<>: 'Text " of type " :<>: ShowType a) ': GetAutoRules xs defs ctx g msg
  GetAutoRules1 r           x a defs ctx g msg xs = '(x, r, a) ': GetAutoRules xs defs ctx g msg


class CompleteChild (nt :: Symbol) (p :: Symbol) (c :: Symbol) (g :: Grammar) where
  augmentChild :: MonadFlow m => Proxy nt -> Proxy p -> Proxy c -> Expr nt p g m a -> [(RuleId, SomeExpr m g)]

instance (KnownSymbol c, MkAutoRules (GetChildAutoRules nt p c g)) => CompleteChild nt p c g where
  augmentChild nt p c e = mkAutoRules (mkAutoP nt p c e) (InhRuleId childname) where
    childname = T.pack $ symbolVal c

    mkAutoP :: Proxy nt -> Proxy p -> Proxy c -> Expr nt p g m a -> Proxy '(GetChildAutoRules nt p c g, m, g)
    mkAutoP _ _ _ _ = Proxy

type GetChildAutoRules nt p c g = GetChildAutoRules1 (GetProd nt p g) (GetInhAttrs nt g) c g ('Text "Missing inherited definition for child " :<>: ShowType c :<>: 'Text " of production " :<>: ShowType p :<>: 'Text " of nonterminal " :<>: ShowType nt)

type family GetChildAutoRules1 prod inhs c g msg where
  GetChildAutoRules1 ('Prod cs locs _ _) inhs c g msg = GetChildAutoRules2 (D.Find c cs) (CtxInh locs inhs) g msg

type family GetChildAutoRules2 child ctx g msg where
  GetChildAutoRules2 ('Child nt' inhs) ctx g msg = GetAutoRules (D.Assocs (GetInhAttrs nt' g)) inhs ctx g msg


class CompleteProd (nt :: Symbol) (p :: Symbol) (g :: Grammar) where
  initProdWithAutoRules :: MonadFlow m => Proxy nt -> Proxy p -> Proxy ty -> Proxy '(m, g) -> Module m g ('SingleDecl ('ProdDecl nt prod ty))

instance (KnownSymbol nt, KnownSymbol p, MkAutoRules (GetProdAutoRules nt p g)) => CompleteProd nt p g where
  initProdWithAutoRules nt p _ resP = Module $ HM.singleton (prodKey nt p) $ HM.fromList $ mkAutoRules (mkAutoP nt p resP) LhsRuleId where
    mkAutoP :: Proxy nt -> Proxy p -> Proxy '(m, g) -> Proxy '(GetProdAutoRules nt p g, m, g)
    mkAutoP _ _ _ = Proxy

type GetProdAutoRules nt p g = GetProdAutoRules1 (GetProd nt p g) (D.Assocs (GetSynAttrs nt g)) g ('Text "Missing synthesized definition for production " :<>: ShowType p :<>: 'Text " of nonterminal " :<>: ShowType nt)

type family GetProdAutoRules1 prod attrs g msg where
  GetProdAutoRules1 ('Prod cs locs lhs _) attrs g msg = GetAutoRules attrs lhs (CtxSyn cs locs) g msg


--
-- Compile
--

newtype Sem (m :: Type -> Type) (g :: Grammar) = Sem (Program m g -> Any -> AttrMap m -> m (AttrMap m))
newtype Program (m :: Type -> Type) (g :: Grammar) = Program (HashMap Text (Sem m g))

type Weave m g = BuildProds (AllProds g) m g

mkHeadP :: Proxy (x ': xs) -> Proxy x
mkHeadP _ = Proxy

mkTailP :: Proxy (x ': xs) -> Proxy xs
mkTailP _ = Proxy

mkFstP :: Proxy '(a, b) -> Proxy a
mkFstP _ = Proxy

mkSndP :: Proxy '(a, b) -> Proxy b
mkSndP _ = Proxy

compile :: Weave m g => Assembly m g g -> Program m g
compile m = buildProds (pAssocs m) m where
  pAssocs :: Assembly m g g -> Proxy (AllProds g)
  pAssocs _ = Proxy

type AllProds g = AllProds1 (D.Assocs g) '[]
type family AllProds1 ns acc where
  AllProds1 ('(nt, ('Nont ps _ _)) ': ns) acc = AllProds2 (A.Assocs ps) nt (AllProds1 ns acc)
  AllProds1 '[] acc = acc

type family AllProds2 ps nt acc where
  AllProds2 ('(p, prod) ': ps) nt acc = '(nt, p, prod) ': AllProds2 ps nt acc
  AllProds2 '[] _ acc = acc

class BuildProds (ps :: ([(Symbol, Symbol, Prod)])) m g where
  buildProds :: Proxy ps -> Assembly m g t -> Program m g

instance BuildProds '[] m g where
  buildProds _ _ = Program HM.empty

instance (KnownSymbol nt, KnownSymbol p, BuildProd '(nt, p, prod) m g, BuildProds ps m g) => BuildProds ('(nt, p, prod) ': ps) m g where
  buildProds p m =
    case buildProds (mkTailP p) m of
      Program pm -> Program $ HM.insert (prodKey (mkNtP p)(mkProdP p)) (buildProd (mkHeadP p) m) pm
    where
      mkNtP :: Proxy ('(nt, p, prod) ': ps) -> Proxy nt
      mkNtP _ = Proxy

      mkProdP :: Proxy ('(nt, p, prod) ': ps) -> Proxy p
      mkProdP _ = Proxy

class MonadFlow m => BuildProd (p :: (Symbol, Symbol, Prod)) m g where
  buildProd :: Proxy p -> Assembly m g t -> Sem m g

instance (KnownSymbol p, KnownSymbol nt, MonadFlow m, BuildChildren (D.Assocs cs) m g, BuildRules (D.Keys locs) m, BuildRules (D.Keys (GetSynAttrs nt g)) m) => BuildProd '(nt, p, 'Prod cs locs syns pty) m g where
  buildProd p m@(Assembly prods) = Sem $ \prog inp inhs -> loop $ \env ->
    do cs   <- buildChildren (mkChildrenP p) (mkEnvP p m) prog rules env
       locs <- buildRules (mkLocsP p)   (mkEnvP p m) LocRuleId rules env
       syns <- buildRules (mkSynsP p m) (mkEnvP p m) LhsRuleId rules env
       env0 <- fork $ pure $ mkEnv (mkEnvP p m) inp cs locs inhs
       pure (syns, env0)
    where
      rules = HM.lookupDefault (error "Internal error: production not in assembly") (prodKey (mkNtP p) (mkProdP p)) prods

      mkChildrenP :: Proxy '(nt, p, 'Prod cs locs syns pty) -> Proxy (D.Assocs cs)
      mkChildrenP _ = Proxy

      mkLocsP :: Proxy '(nt, p, 'Prod cs locs syns pty) -> Proxy (D.Keys locs)
      mkLocsP _ = Proxy

      mkSynsP :: Proxy '(nt, p, prod) -> Assembly m g t -> Proxy (D.Keys (GetSynAttrs nt g))
      mkSynsP _ _ = Proxy

      mkEnvP :: Proxy '(nt, p, prod) -> Assembly m g t -> Proxy (Env m nt p g)
      mkEnvP _ _ = Proxy

      mkNtP :: Proxy '(nt, p, prod) -> Proxy nt
      mkNtP _ = Proxy

      mkProdP :: Proxy '(nt, p, prod) -> Proxy p
      mkProdP _ = Proxy

mkEnv :: Proxy (Env m nt p g) -> Any -> BranchMap m (AttrMap m) -> AttrMap m -> AttrMap m -> Env m nt p g
mkEnv _ = Env

class BuildRules (xs :: [Symbol]) m where
  buildRules :: Proxy xs -> Proxy (Env m nt p g) -> (Text -> RuleId) -> Rules m g -> Branch m (Env m nt p g) -> m (AttrMap m)

instance MonadFlow m => BuildRules '[] m where
  buildRules _ _ _ _ _ = pure HM.empty

instance (KnownSymbol x, MonadFlow m, BuildRules xs m) => BuildRules (x ': xs) m where
  buildRules ps pEnv mkRuleId rules env
    = do r <- fork $
          do env1 <- merge env
             runReaderT m env1
         rs <- buildRules (mkTailP ps) pEnv mkRuleId rules env
         pure $ HM.insert attrname r rs
    where
      attrname = T.pack $ symbolVal $ mkHeadP ps
      ruleId   = mkRuleId attrname
      (Expr m) = unsafeFromSomeExpr $ HM.lookupDefault (error $ "Rule not implemented: " ++ show ruleId) ruleId rules

class BuildChildren (cs :: [(Symbol, Child)]) m g where
  buildChildren :: Proxy cs -> Proxy (Env m nt p g) -> Program m g -> Rules m g -> Branch m (Env m nt p g) -> m (BranchMap m (AttrMap m))

instance MonadFlow m => BuildChildren '[] m g where
  buildChildren _ _ _ _ _ = pure HM.empty

instance (KnownSymbol c, KnownSymbol nt', MonadFlow m, BuildRules (D.Keys (GetInhAttrs nt' g)) m, BuildChildren cs m g) => BuildChildren ('(c, 'Child nt' inhs) ': cs) m g where
  buildChildren ps pEnv prog@(Program sems) rules env
    = do inhs <- buildRules (mkInhP ps prog) pEnv (InhRuleId childname) rules env
         c <- fork $
          do env1 <- merge env
             ProdCon pn inp wrap <- runReaderT childdef env1
             let Sem sem = HM.lookupDefault (error "Internal error: semfun not in program") (prodKey' (mkNtP ps) pn) sems
             wrap (sem prog inp) inhs
         cs <- buildChildren (mkTailP ps) pEnv prog rules env
         pure $ HM.insert childname c cs
    where
      childname = T.pack $ symbolVal $ mkFstP $ mkHeadP ps
      ruleId = ChildRuleId childname
      (Expr childdef) = unsafeFromSomeExpr $ HM.lookupDefault (error $ "Rule not implemented: " ++ show ruleId) ruleId rules

      mkNtP :: Proxy ('(c, 'Child nt' inhs) ': cs) -> Proxy nt'
      mkNtP _ = Proxy

      mkInhP :: Proxy ('(c, 'Child nt' inhs) ': cs) -> Program m g -> Proxy (D.Keys (GetInhAttrs nt' g))
      mkInhP _ _ = Proxy


weave :: (Compile ds EmptyGrammar ~ g, Weave m g) => Module m g ds -> Program m g
weave = compile . assemble


--
-- Evaluation
--

eval :: (KnownSymbol nt, KnownSymbol p, MonadFlow m, ValidProdRef nt p g a) => Program m g -> Proxy nt -> Proxy p -> a -> D.Rec (D.Normalize (AppBranch m (GetInhAttrs nt g))) -> m (D.Rec (D.Normalize (AppBranch m (GetSynAttrs nt g))))
eval prog@(Program prods) nt prod a inhs
  = D.unsafeFromAssocs <$> sem prog (unsafeCoerce a) (unsafeToAttrMap prog $ D.assocs inhs)
  where
    (Sem sem) = prods HM.! prodKey nt prod
    unsafeToAttrMap :: Program m g -> HashMap Text Any -> AttrMap m
    unsafeToAttrMap _ m = unsafeCoerce m


--
-- Labels
--

root :: Proxy "root"
root = Proxy

lhs :: Proxy "lhs"
lhs = Proxy

loc :: Proxy "loc"
loc = Proxy

genLabel :: String -> Q [Dec]
genLabel s = sequence
  [ sigD (mkName s) (appT (conT $ mkName "Proxy") (litT $ strTyLit s))
  , valD (varP $ mkName s) (normalB $ conE $ mkName "Proxy") []
  ]

genLabels :: [String] -> Q [Dec]
genLabels ss = concat <$> mapM genLabel ss


--
-- Lists and maps
--

cons :: Proxy "cons"
cons = Proxy

nil  :: Proxy "nil"
nil = Proxy

hd :: Proxy "hd"
hd = Proxy

tl :: Proxy "tl"
tl = Proxy

key :: Proxy "key"
key = Proxy

val :: Proxy "val"
val = Proxy

mkList :: (Monad m, KnownSymbol nt, ValidProdRef nt "nil" g (), ValidProdRef nt "cons" g (t, [t])) =>
  Proxy nt -> [t] -> Expr nt' prod' g m (ProdCon m nt)
mkList listNt xs
  = case xs of
      []      -> prod listNt nil ()
      (x:xs') -> prod listNt cons (x, xs')


type DeclListConstr m nt childNt g t =
  ( MonadFlow m
  , (GetProdType nt "cons" g) ~ (t, [t])
  , KnownSymbol childNt, KnownSymbol nt
  , ValidChildType g nt "cons" "hd" childNt
  , ValidChildType g nt "cons" "tl" nt
  , CompleteChild nt "cons" "hd" g
  , CompleteProd nt "nil" g
  , CompleteProd nt "cons" g
  , CompleteChild nt "cons" "tl" g
  , ValidLocType 'False g nt "cons" "val" t t
  , ValidAttrRef nt "cons" "loc" "val" g t
  , ValidProdRef nt "nil" g ()
  , ValidProdRef nt "cons" g (t, [t])
  )

type DeclListType m nt childNt g t =
  Proxy childNt -> Proxy nt -> (t -> Expr nt "cons" g m (ProdCon m childNt)) ->
    Module m g
      ( 'ComposeDecls
          'EmptyDecls
          ('ComposeDecls
             ('ComposeDecls
                ('ComposeDecls
                   ('SingleDecl ('NontDecl nt))
                   ('SingleDecl ('ProdDecl nt "nil" ())))
                ('SingleDecl ('ProdDecl nt "cons" (t, [t]))))
             ('ComposeDecls
                'EmptyDecls
                ('ComposeDecls
                   ('SingleDecl ('LocDef nt "cons" "val" t))
                   ('ComposeDecls
                      ('SingleDecl ('ChildDef nt "cons" "hd" childNt))
                      ('SingleDecl ('ChildDef nt "cons" "tl" nt)))))))

declList :: DeclListConstr m nt childNt g t => DeclListType m nt childNt g t
declList elemNt listNt f
  =  emptyModule Proxy
  §§ productions listNt
     &| nil
     &| cons
  §§ rules listNt cons
     § loc ?  val    := (fst <$> this)
     § hd  ?: elemNt := (loc ! val >>= f)
     § tl  ?: listNt := (this >>= mkList listNt . snd)

mkMap :: (Monad m, KnownSymbol nt, ValidProdRef nt "nil" g (), ValidProdRef nt "cons" g ((k,t), [(k,t)])) =>
  Proxy nt -> Map k t -> Expr nt' prod' g m (ProdCon m nt)
mkMap nt = mkList nt . M.assocs

declMap :: (DeclListConstr m nt childNt g (k, t)) => DeclListType m nt childNt g (k, t)
declMap = declList


--
-- Sinks: collect inherited attributes into a single synthesized attribute
--

declSink ::
  ( MonadFlow m, KnownSymbol nt, CompleteProd nt "nil" g, ValidLocType 'False g nt "nil" "val" (D.Rec t') (D.Rec t')
  , (AppBranch m (GetInhAttrs nt g)) ~ t, t' ~ D.Normalize t) => Proxy nt -> Module m g
      ('ComposeDecls
         'EmptyDecls
         ('ComposeDecls
            ('ComposeDecls
               ('SingleDecl ('NontDecl nt))
               ('SingleDecl ('ProdDecl nt "nil" ())))
            ('ComposeDecls
               ('ComposeDecls
                  'EmptyDecls
                  ('SingleDecl ('SynDecl nt "val" (D.Rec t'))))
               ('ComposeDecls
                  'EmptyDecls
                  ('SingleDecl
                     ('LocDef
                        nt "nil" "val" (D.Rec t')))))))

declSink nt
  = emptyModule Proxy
  §§ productions nt &| nil
  §§ attributes nt
     § syn val
  §§ rules nt nil
     § loc ? val := attrs lhs
