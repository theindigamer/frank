-- The raw abstract syntax and (refined) abstract syntax for Frank
{-# LANGUAGE GADTs,
             StandaloneDeriving,
             FlexibleInstances, UndecidableInstances,
             DataKinds, KindSignatures, ConstraintKinds,
             LambdaCase,
             PatternSynonyms #-}
module Syntax where

import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Maybe (fromMaybe)
import Data.List
import Data.Functor.Identity
import Data.Kind (Constraint, Type)
import Data.Coerce (coerce, Coercible)

import BwdFwd

import Shonky.Renaming

{-# ANN module "HLint: ignore Use camelCase" #-}

--------------------------------------------------------------------------------
-- * Elementary definitions

-- | lol.
type Identifier = String

-- | Top level definitions instantiate this class
class HasIdentifier a where
  getIdentifier :: a -> Identifier

----------------------------------------------------------------------
-- * Fix points and annotations

-- | Fixed-point operator, takes a functor @f@
newtype Fix f = MkFix (f (Fix f))

deriving instance Show (f (Fix f)) => Show (Fix f)
deriving instance Eq (f (Fix f)) => Eq (Fix f)

type Transformer = (Type -> Type) -> (Type -> Type)

-- | Gives the fixed-point of a functor "f" (see AST definitions),
-- parameterised by transformer "t" (e.g. AnnotT Raw).
type TFix (t :: Transformer)
          (f :: Transformer -> Type -> Type) = Fix (t (f t))

-- | Annotation Transformer.
-- Takes an annotation object @a@, a functor @f@, recursor type @r@.
newtype AnnotT a f r = MkAnnotT (f r, a)
  deriving (Show, Eq)

-- | Like TFix, but with special transformer, namely @AnnotT a@
-- Takes an annotation object @a@, a functor @f@.
type AnnotTFix a f = TFix (AnnotT a) f

-- | Add annotation.
ann :: a -> f (AnnotT a) (AnnotTFix a f) -> AnnotTFix a f
ann a v = MkFix (MkAnnotT (v, a))

-- | Retrieve object + annotation.
unwrap :: AnnotTFix a f -> (f (AnnotT a) (AnnotTFix a f), a)
unwrap (MkFix (MkAnnotT (v, a))) = (v, a)

-- | Strip annotation.
stripAnn :: AnnotTFix a f -> f (AnnotT a) (AnnotTFix a f)
stripAnn = fst . unwrap

-- | Get annotation.
getAnn :: AnnotTFix a f -> a
getAnn = snd . unwrap

-- | Set annotation, dropping the existing one.
setAnn :: a -> AnnotTFix a f -> AnnotTFix a f
setAnn a = ann a . stripAnn

-- | To annotate the origin of a node
data Source
  = InCode (Int, Int)
  | BuiltIn
  | Implicit
  | ImplicitNear (Int, Int)
  | Generated
  deriving (Show, Eq)

class HasSource a where
  getSource :: a -> Source

instance {-# OVERLAPPABLE #-} Coercible Source a => HasSource a where
  getSource = coerce

instance HasSource a => HasSource (AnnotTFix a f) where
  getSource x = getSource (getAnn x)

-- NOTE (Varun): Erm, why is this changing things?
implicitNear :: HasSource a => a -> Source
implicitNear v = case getSource v of
  InCode (line, col) -> ImplicitNear (line, col)
  _                  -> Implicit

--------------------------------------------------------------------------------
-- * Stage-wise annotations.
--
-- Raw syntax comes from the parser and is preprocessed into Refined syntax.
-- After that, Refined syntax gets converted to Desugared syntax.
--
-- GADTs are used to enforce the fact that only certain constructors are present
-- at different stages.
--
-- We use @syn@ as the type variable for the "syntax state".
-- So, @syn@ will be one of 'Raw', 'Refined', or 'Desugared'.

-- | Output from the parser
newtype Raw = Raw Source
  deriving (Show, Eq)

class NotRaw a where
instance NotRaw () where
-- TODO (Varun): This instance below seems fishy. Shouldn't it be only
-- present for a ~ Desugared and a ~ Refined?
instance NotRaw (AnnotT a Identity ()) where
instance NotRaw Desugared where
instance NotRaw Refined where

type IsNotRaw t = NotRaw (t Identity ())

-- | Well-formed AST, after tidying up the output from the parser.
newtype Refined = Refined Source
  deriving (Show, Eq)

class NotDesugared a where
instance NotDesugared Raw where
instance NotDesugared (AnnotT Raw Identity ()) where
instance NotDesugared Refined where
instance NotDesugared (AnnotT Refined Identity ()) where

-- | Desugaring of types:
--   * type variables are given unique names
--   * strings are lists of characters -- NOTE (Varun): Erm, what?
newtype Desugared = Desugared Source
  deriving (Show, Eq)

--------------------------------------------------------------------------------
-- * AST Nodes

-- TODO (Varun): Understand this comment...
-- Parts of the grammar are specific to raw/refined/desugared syntax.
-- The following markings are used:
-- - require Raw/Refined/Desugared:   t = AnnotT Raw
-- - require NotRaw / NotDesugared:   IsNotRaw t =>   annotation

-- | The program is just a list of terms.
newtype Program t = MkProgram [TopTerm t]
  deriving (Show, Eq)

----------------------------------------------------------------------
-- ** Nodes specific to Raw syntax.

-- | A top-level multihandler signature and clause.
data MultiHandlerSignatureF :: Transformer -> * -> * where
  MkMultiHandlerSignature
    :: Identifier -> CompType Raw -> MultiHandlerSignatureF (AnnotT Raw) r

deriving instance
  (Show r, Show (TFix t MultiHandlerSignatureF)) => Show (MultiHandlerSignatureF t r)
deriving instance
  (Eq r, Eq (TFix t MultiHandlerSignatureF)) => Eq (MultiHandlerSignatureF t r)

type MultiHandlerSignature p = AnnotTFix p MultiHandlerSignatureF

pattern MkSig :: syn ~ Raw => Identifier -> CompType Raw -> syn -> MultiHandlerSignature syn
pattern MkSig x cty a = MkFix (MkAnnotT (MkMultiHandlerSignature x cty, a))

instance syn ~ Raw => HasIdentifier (MultiHandlerSignature syn) where
  getIdentifier (MkSig x _ _) = x

data MultiHandlerClauseF :: Transformer -> * -> * where
  MkMultiHandlerClause
    :: Identifier -> Clause Raw -> MultiHandlerClauseF (AnnotT Raw) r

deriving instance
  (Show r, Show (TFix t MultiHandlerClauseF)) => Show (MultiHandlerClauseF t r)
deriving instance
  (Eq r, Eq (TFix t MultiHandlerClauseF)) => Eq (MultiHandlerClauseF t r)

type MultiHandlerClause a = AnnotTFix a MultiHandlerClauseF

pattern MkMHClause :: syn ~ Raw => Identifier -> Clause Raw -> syn -> MultiHandlerClause syn
pattern MkMHClause x cls a = MkFix (MkAnnotT (MkMultiHandlerClause x cls, a))

instance syn ~ Raw => HasIdentifier (MultiHandlerClause syn) where
  getIdentifier (MkMHClause x _ _) = x

----------------------------------------------------------------------
-- ** Nodes specific to Refined syntax.

------------------------------------------------------------
-- *** Multi-handler definitions
-- NOTE: Multi-handler here = "operator" in the paper.

-- FIXME: currently all top-level bindings are mutually
-- recursive. This setup will break if we add non-recursive value
-- bindings.
--
-- An obvious design is to group mutually recursive bindings using
-- letrec, as specified in the paper.
--
-- Data and interface definitions can continue to be globally mutually
-- recursive as they do not depend on values.

data MultiHandlerDefinitionF :: Transformer -> * -> * where
  MkMultiHandlerDefinition
    :: Identifier
    -> TFix t CompTypeF
    -> [TFix t ClauseF]
    -> MultiHandlerDefinitionF t r

type MultiHandlerDefinitionF_ClassReq (c :: Type -> Constraint) r t
  = ( c (TFix t CompTypeF)
    , c (TFix t ClauseF)
    , c r, c (TFix t MultiHandlerDefinitionF)
    )

deriving instance
  MultiHandlerDefinitionF_ClassReq Show r t => Show (MultiHandlerDefinitionF t r)
deriving instance
  MultiHandlerDefinitionF_ClassReq Eq r t => Eq (MultiHandlerDefinitionF t r)

type MultiHandlerDefinition a = AnnotTFix a MultiHandlerDefinitionF

pattern MkDef :: Identifier -> CompType syn -> [Clause syn] -> syn -> MultiHandlerDefinition syn
pattern MkDef x cty clss a = MkFix (MkAnnotT (MkMultiHandlerDefinition x cty clss, a))

instance HasIdentifier (MultiHandlerDefinition t) where
  getIdentifier (MkDef x _ _ _) = x

------------------------------------------------------------
-- *** Operators
-- Operator here doesn't have a name in the paper, it is a subset of Uses.

data OperatorF :: Transformer -> * -> * where
  -- | Monotypic (just variable)
  MkMono          :: Identifier -> OperatorF t r
  -- | Polytypic (handler expecting arguments, could also be 0 args (!))
  MkPoly          :: Identifier -> OperatorF t r
  -- | ...
  MkCmdIdentifier :: Identifier -> OperatorF t r

deriving instance (Show r, Show (TFix t OperatorF)) => Show (OperatorF t r)
deriving instance (Eq r, Eq (TFix t OperatorF)) => Eq (OperatorF t r)

type Operator a = AnnotTFix a OperatorF

pattern Mono x a = MkFix (MkAnnotT (MkMono x, a))
pattern Poly x a = MkFix (MkAnnotT (MkPoly x, a))
pattern CmdIdentifier x a = MkFix (MkAnnotT (MkCmdIdentifier x, a))

------------------------------------------------------------
-- *** Data constructors

data DataConF :: Transformer -> * -> * where
  MkDataCon :: Identifier -> [TFix t TermF] -> DataConF t r

type DataConF_ClassReq (c :: Type -> Constraint) r t
  = ( c (TFix t TermF)
    , c r, c (TFix t DataConF)
    )

deriving instance DataConF_ClassReq Show r t => Show (DataConF t r)
deriving instance DataConF_ClassReq Eq r t   => Eq (DataConF t r)

type DataCon a = AnnotTFix a DataConF

pattern DataCon :: Identifier -> [Term ann] -> ann -> DataCon ann
pattern DataCon x tms a = MkFix (MkAnnotT (MkDataCon x tms, a))

----------------------------------------------------------------------
-- ** Nodes independent of syntax.

------------------------------------------------------------
-- *** Top-level terms

-- | A raw term collects multihandler signatures and clauses separately. A
-- refined top-level term collects multihandler signatures and clauses in
-- one definition.
data TopTermF :: Transformer -> Type -> Type where
  MkDataTerm     :: TFix t DataTF    -> TopTermF t r
  MkInterfaceTerm      :: TFix t InterfaceF      -> TopTermF t r
  MkInterfaceAliasTerm :: TFix t InterfaceAliasF -> TopTermF t r

  MkSigTerm    :: t ~ AnnotT Raw => TFix t MultiHandlerSignatureF -> TopTermF t r
  MkMHClauseTerm :: t ~ AnnotT Raw => TFix t MultiHandlerClauseF    -> TopTermF t r

  MkDefTerm    :: IsNotRaw t => TFix t MultiHandlerDefinitionF -> TopTermF t r
  -- MkDefTerm :: NotRaw t => MHDef t -> TopTermF t r

type TopTermF_ClassReq (c :: Type -> Constraint) r t =
  ( c (TFix t DataTF)
  , c (TFix t InterfaceF)
  , c (TFix t InterfaceAliasF)
  , c (TFix (AnnotT Raw) MultiHandlerSignatureF)
  , c (TFix (AnnotT Raw) MultiHandlerClauseF)
  , c (TFix t MultiHandlerDefinitionF)
  , c r, c (TFix t TopTermF)
  )

deriving instance TopTermF_ClassReq Show r t => Show (TopTermF t r)
deriving instance TopTermF_ClassReq Eq r t   => Eq (TopTermF t r)

type TopTerm a = AnnotTFix a TopTermF

pattern DataTerm dt a = MkFix (MkAnnotT (MkDataTerm dt, a))
pattern InterfaceTerm itf a = MkFix (MkAnnotT (MkInterfaceTerm itf, a))
pattern InterfaceAliasTerm itfAl a = MkFix (MkAnnotT (MkInterfaceAliasTerm itfAl, a))
pattern SigTerm sig a    = MkFix (MkAnnotT (MkSigTerm sig,    a))
pattern ClauseTerm cls a = MkFix (MkAnnotT (MkMHClauseTerm cls, a))
pattern DefTerm def a    = MkFix (MkAnnotT (MkDefTerm def,    a))

-- TODO: LC: Automatic generation of the following? Should be possible
--           somehow

instance HasIdentifier (TopTerm t) where
  getIdentifier (DataTerm dt _)        = getIdentifier dt
  getIdentifier (InterfaceTerm itf _)        = getIdentifier itf
  getIdentifier (InterfaceAliasTerm itfAl _) = getIdentifier itfAl
  getIdentifier (SigTerm sig _)        = getIdentifier sig
  getIdentifier (ClauseTerm cls _)     = getIdentifier cls
  getIdentifier (DefTerm def _)        = getIdentifier def

------------------------------------------------------------
-- *** Uses

data UseF :: Transformer -> * -> * where
  MkRawIdentifier :: t ~ AnnotT Raw => Identifier          -> UseF t r
  MkRawComb       :: t ~ AnnotT Raw => r -> [TFix t TermF] -> UseF t r
  MkOp            :: IsNotRaw t     => TFix t OperatorF    -> UseF t r
  MkApp           :: IsNotRaw t     => r -> [TFix t TermF] -> UseF t r
  MkAdapted       :: [TFix t AdaptorF] -> r                -> UseF t r

type UseF_ClassReq (c :: Type -> Constraint) r t =
  ( c (TFix t OperatorF)
  , c (TFix t TermF)
  , c (TFix t InterfaceMapF)
  , c (TFix t AdaptorF)
  , c r, c (TFix t UseF)
  )

deriving instance UseF_ClassReq Show r t => Show (UseF t r)
deriving instance UseF_ClassReq Eq r t   => Eq   (UseF t r)

type Use a = AnnotTFix a UseF
pattern RawIdentifier x a = MkFix (MkAnnotT (MkRawIdentifier x, a))
pattern RawComb f xs a = MkFix (MkAnnotT (MkRawComb f xs, a))
pattern Op op a = MkFix (MkAnnotT (MkOp op, a))
pattern App f xs a = MkFix (MkAnnotT (MkApp f xs, a))
pattern Adapted rs tm a = MkFix (MkAnnotT (MkAdapted rs tm, a))

------------------------------------------------------------
-- *** Terms
-- This corresponds to "construction" in the paper

data TermF :: Transformer -> * -> * where
  MkSC :: TFix t SCompF -> TermF t r
  MkLet :: Identifier -> r -> r -> TermF (AnnotT Raw) r
  MkStr :: String -> TermF t r
  MkInt :: Int -> TermF t r
  MkChar :: Char -> TermF t r
  MkList :: [r] -> TermF (AnnotT Raw) r
  MkTermSeq :: r -> r -> TermF t r
  MkUse :: TFix t UseF -> TermF t r
  MkDCon :: IsNotRaw t => TFix t DataConF -> TermF t r

type TermF_ClassReq (c :: Type -> Constraint) r t =
  ( c (TFix t SCompF)
  , c (TFix t UseF)
  , c (TFix t DataConF)
  , c r, c (TFix t TermF)
  )

deriving instance TermF_ClassReq Show r t => Show (TermF t r)
deriving instance TermF_ClassReq Eq   r t => Eq (TermF t r)

type Term a = AnnotTFix a TermF
pattern SC sc a = MkFix (MkAnnotT (MkSC sc, a))
pattern Let x tm1 tm2 a = MkFix (MkAnnotT (MkLet x tm1 tm2, a))
pattern StrTerm str a = MkFix (MkAnnotT (MkStr str, a))
pattern IntTerm n a = MkFix (MkAnnotT (MkInt n, a))
pattern CharTerm c a = MkFix (MkAnnotT (MkChar c, a))
pattern ListTerm xs a = MkFix (MkAnnotT (MkList xs, a))
pattern TermSeq tm1 tm2 a = MkFix (MkAnnotT (MkTermSeq tm1 tm2, a))
pattern Use u a = MkFix (MkAnnotT (MkUse u, a))
pattern DCon dc a = MkFix (MkAnnotT (MkDCon dc, a))

------------------------------------------------------------
-- *** Clauses for multi-handler definitions

-- A clause for a multihandler definition
data ClauseF :: Transformer -> * -> * where
  MkClauseF :: [TFix t PatternF] -> TFix t TermF -> ClauseF t r

type Clause_ClassReq (c :: Type -> Constraint) r t =
  ( c (TFix t PatternF)
  , c (TFix t TermF)
  , c r, c (TFix t ClauseF)
  )

deriving instance Clause_ClassReq Show r t => Show (ClauseF t r)
deriving instance Clause_ClassReq Eq   r t => Eq (ClauseF t r)

type Clause a = AnnotTFix a ClauseF

pattern MkClause :: [Pattern syn] -> Term syn -> syn -> Clause syn
pattern MkClause ps t a = MkFix (MkAnnotT (MkClauseF ps t, a))

------------------------------------------------------------
-- *** Suspended computations

data SCompF :: Transformer -> * -> * where
  MkSComp :: [TFix t ClauseF] -> SCompF t r

deriving instance (Show (TFix t ClauseF),
                   Show r, Show (TFix t SCompF)) => Show (SCompF t r)
deriving instance (Eq (TFix t ClauseF),
                   Eq r, Eq (TFix t SCompF)) => Eq (SCompF t r)
type SComp a = AnnotTFix a SCompF
pattern SComp cls a = MkFix (MkAnnotT (MkSComp cls, a))

------------------------------------------------------------
-- *** Data types

data Kind
  = VT -- ^ value type
  | ET -- ^ effect type
  deriving (Show, Eq)

data DataTF :: Transformer -> * -> * where
  MkDT :: Identifier -> [(Identifier, Kind)] -> [TFix t CtrF] -> DataTF t r
deriving instance (Show (TFix t CtrF),
                   Show r, Show (TFix t DataTF)) => Show (DataTF t r)
deriving instance (Eq (TFix t CtrF),
                   Eq r, Eq (TFix t DataTF)) => Eq (DataTF t r)
type DataT a = AnnotTFix a DataTF
pattern DT x ps ctrs a = MkFix (MkAnnotT (MkDT x ps ctrs, a))
instance HasIdentifier (DataT t) where getIdentifier (DT x _ _ _) = x

------------------------------------------------------------
-- *** Interfaces

data InterfaceF :: Transformer -> * -> * where
  MkInterfaceF :: Identifier -> [(Identifier, Kind)] -> [TFix t CmdF] -> InterfaceF t r

deriving instance (Show (TFix t CmdF),
                   Show r, Show (TFix t InterfaceF)) => Show (InterfaceF t r)
deriving instance (Eq (TFix t CmdF),
                   Eq r, Eq (TFix t InterfaceF)) => Eq (InterfaceF t r)
type Interface a = AnnotTFix a InterfaceF

pattern MkInterface x ps cmds a = MkFix (MkAnnotT (MkInterfaceF x ps cmds, a))
instance HasIdentifier (Interface t) where getIdentifier (MkInterface x _ _ _) = x

data InterfaceAliasF :: Transformer -> * -> * where
  MkInterfaceAliasF
    :: Identifier -> [(Identifier, Kind)] -> TFix t InterfaceMapF -> InterfaceAliasF t r

deriving instance (Show (TFix t InterfaceMapF),
                   Show r, Show (TFix t InterfaceAliasF)) => Show (InterfaceAliasF t r)
deriving instance (Eq (TFix t InterfaceMapF),
                   Eq r, Eq (TFix t InterfaceAliasF)) => Eq (InterfaceAliasF t r)

type InterfaceAlias a = AnnotTFix a InterfaceAliasF

pattern MkInterfaceAlias x ps itfMap a = MkFix (MkAnnotT (MkInterfaceAliasF x ps itfMap, a))

instance HasIdentifier (InterfaceAlias t) where
  getIdentifier (MkInterfaceAlias x _ _ _) = x

data CtrF :: Transformer -> * -> * where
  MkCtr :: Identifier -> [TFix t ValueTypeF] -> CtrF t r
deriving instance (Show (TFix t ValueTypeF),
                   Show r, Show (TFix t CtrF)) => Show (CtrF t r)
deriving instance (Eq (TFix t ValueTypeF),
                   Eq r, Eq (TFix t CtrF)) => Eq (CtrF t r)
type Ctr a = AnnotTFix a CtrF
pattern Ctr x tys a = MkFix (MkAnnotT (MkCtr x tys, a))

data CmdF :: Transformer -> * -> * where
  MkCmd :: Identifier -> [(Identifier, Kind)] -> [TFix t ValueTypeF] -> TFix t ValueTypeF ->
           CmdF t r
deriving instance (Show (TFix t ValueTypeF),
                   Show r, Show (TFix t CmdF)) => Show (CmdF t r)
deriving instance (Eq (TFix t ValueTypeF),
                   Eq r, Eq (TFix t CmdF)) => Eq (CmdF t r)
--                    id  ty vars      arg tys   result ty
type Cmd a = AnnotTFix a CmdF
pattern Cmd x ps tys ty a = MkFix (MkAnnotT (MkCmd x ps tys ty, a))

data PatternF :: Transformer -> * -> * where
  MkVPat :: TFix t ValuePatF -> PatternF t r
  MkCmdPat :: Identifier -> Int -> [TFix t ValuePatF] -> Identifier -> PatternF t r
  MkThkPat :: Identifier -> PatternF t r
deriving instance (Show (TFix t ValuePatF),
                   Show r, Show (TFix t PatternF)) => Show (PatternF t r)
deriving instance (Eq (TFix t ValuePatF),
                   Eq r, Eq (TFix t PatternF)) => Eq (PatternF t r)
type Pattern a = AnnotTFix a PatternF
pattern VPat vp a = MkFix (MkAnnotT (MkVPat vp, a))
pattern CmdPat x n vps k a = MkFix (MkAnnotT (MkCmdPat x n vps k, a))
pattern ThkPat x a = MkFix (MkAnnotT (MkThkPat x, a))

-- TODO: should we compile away string patterns into list of char patterns?
-- Takes      tag "t" (e.g. Refined),
--       recursor "r"
data ValuePatF :: Transformer -> * -> * where
  MkVarPat :: Identifier -> ValuePatF t r
  MkDataPat :: Identifier -> [r] -> ValuePatF t r
  MkIntPat :: Int -> ValuePatF t r
  MkCharPat :: Char -> ValuePatF t r
  MkStrPat :: String -> ValuePatF t r
  MkConsPat :: r -> r -> ValuePatF (AnnotT Raw) r
  MkListPat :: [r] -> ValuePatF (AnnotT Raw) r
deriving instance (Show r, Show (TFix t ValuePatF)) => Show (ValuePatF t r)
deriving instance (Eq r, Eq (TFix t ValuePatF)) => Eq (ValuePatF t r)
type ValuePat a = AnnotTFix a ValuePatF
pattern VarPat x a = MkFix (MkAnnotT (MkVarPat x, a))
pattern DataPat x vps a = MkFix (MkAnnotT (MkDataPat x vps, a))
pattern IntPat n a = MkFix (MkAnnotT (MkIntPat n, a))
pattern CharPat c a = MkFix (MkAnnotT (MkCharPat c, a))
pattern StrPat str a = MkFix (MkAnnotT (MkStrPat str, a))
pattern ConsPat p1 p2 a = MkFix (MkAnnotT (MkConsPat p1 p2, a))
pattern ListPat ps a = MkFix (MkAnnotT (MkListPat ps, a))

-- Type hierarchy
data CompTypeF :: Transformer -> * -> * where
  MkCompType :: [TFix t PortF] -> TFix t PegF -> CompTypeF t r -- computation types

deriving instance (Show (TFix t PortF),
                   Show (TFix t PegF),
                   Show r, Show (TFix t CompTypeF)) => Show (CompTypeF t r)
deriving instance (Eq (TFix t PortF),
                   Eq (TFix t PegF),
                   Eq r, Eq (TFix t CompTypeF)) => Eq (CompTypeF t r)

type CompType a = AnnotTFix a CompTypeF

pattern CompType ports peg a = MkFix (MkAnnotT (MkCompType ports peg, a))

data PortF :: Transformer -> * -> * where
  MkPort :: [TFix t AdjustmentF] -> TFix t ValueTypeF -> PortF t r              -- ports
deriving instance (Show (TFix t AdjustmentF),
                   Show (TFix t ValueTypeF),
                   Show r, Show (TFix t PortF)) => Show (PortF t r)
deriving instance (Eq (TFix t AdjustmentF),
                   Eq (TFix t ValueTypeF),
                   Eq r, Eq (TFix t PortF)) => Eq (PortF t r)
type Port a = AnnotTFix a PortF
pattern Port adjs ty a = MkFix (MkAnnotT (MkPort adjs ty, a))

data PegF :: Transformer -> * -> * where
  MkPeg :: TFix t AbF -> TFix t ValueTypeF -> PegF t r                          -- pegs
deriving instance (Show (TFix t AbF),
                   Show (TFix t ValueTypeF),
                   Show r, Show (TFix t PegF)) => Show (PegF t r)
deriving instance (Eq (TFix t AbF),
                   Eq (TFix t ValueTypeF),
                   Eq r, Eq (TFix t PegF)) => Eq (PegF t r)
type Peg a = AnnotTFix a PegF
pattern Peg ab ty a = MkFix (MkAnnotT (MkPeg ab ty, a))

-- | Value types
data ValueTypeF :: Transformer -> * -> * where
  -- | Data types (instant. type constr.) may be refined to MkTVar
  MkDTTy :: Identifier -> [TFix t TypeArgF] -> ValueTypeF t r
  -- | Suspended computation types
  MkSCTy :: TFix t CompTypeF -> ValueTypeF t  r
  -- | May be refined to MkDTTy
  MkTVar :: NotDesugared (t Identity ()) => Identifier -> ValueTypeF t  r
  -- | Rigid type variable (bound)
  MkRTVar :: Identifier -> ValueTypeF (AnnotT Desugared)  r
  -- | Flexible type variable (free)
  MkFTVar :: Identifier -> ValueTypeF (AnnotT Desugared)  r
  -- | String type
  MkStringTy :: NotDesugared (t Identity ()) => ValueTypeF t r
  -- | Int type
  MkIntTy :: ValueTypeF t r
  -- | Char type
  MkCharTy :: ValueTypeF t r

deriving instance (Show (TFix t TypeArgF),
                   Show (TFix t CompTypeF),
                   Show r, Show (TFix t ValueTypeF)) => Show (ValueTypeF t r)
deriving instance (Eq (TFix t TypeArgF),
                   Eq (TFix t CompTypeF),
                   Eq r, Eq (TFix t ValueTypeF)) => Eq (ValueTypeF t r)

type ValueType a = AnnotTFix a ValueTypeF
pattern DTTy x tyArgs a = MkFix (MkAnnotT (MkDTTy x tyArgs, a))
pattern SCTy cty a = MkFix (MkAnnotT (MkSCTy cty, a))
pattern TVar x a = MkFix (MkAnnotT (MkTVar x, a))
pattern RTVar x a = MkFix (MkAnnotT (MkRTVar x, a))
pattern FTVar x a = MkFix (MkAnnotT (MkFTVar x, a))
pattern StringTy a = MkFix (MkAnnotT (MkStringTy, a))
pattern IntTy a = MkFix (MkAnnotT (MkIntTy, a))
pattern CharTy a = MkFix (MkAnnotT (MkCharTy, a))

-- Interface-id -> list of bwd-list of ty arg's (each entry an instantiation)
data InterfaceMapF :: Transformer -> * -> * where
  MkInterfaceMap :: M.Map Identifier (Bwd [TFix t TypeArgF]) -> InterfaceMapF t r

deriving instance (Show (TFix t TypeArgF),
                   Show r, Show (TFix t InterfaceMapF)) => Show (InterfaceMapF t r)
deriving instance (Eq (TFix t TypeArgF),
                   Eq r, Eq (TFix t InterfaceMapF)) => Eq (InterfaceMapF t r)

type InterfaceMap a = AnnotTFix a InterfaceMapF
pattern InterfaceMap m a = MkFix (MkAnnotT (MkInterfaceMap m, a))

------------------------------------------------------------
-- *** Adjustments

data AdjustmentF :: Transformer -> * -> * where
  MkConsAdj
    :: Identifier        -- ^ interface-id
    -> [TFix t TypeArgF] -- ^ list of type arguments
    -> AdjustmentF t r
  MkAdaptorAdj :: TFix t AdaptorF -> AdjustmentF t r

type Adjustment_ClassReq (c :: Type -> Constraint) r t =
  ( c (TFix t TypeArgF)
  , c (TFix t AdaptorF)
  , c r, c (TFix t AdjustmentF)
  )

deriving instance Adjustment_ClassReq Show r t => Show (AdjustmentF t r)
deriving instance Adjustment_ClassReq Eq   r t => Eq (AdjustmentF t r)

type Adjustment a = AnnotTFix a AdjustmentF

pattern ConsAdj x ts a = MkFix (MkAnnotT (MkConsAdj x ts, a))
pattern AdaptorAdj adp a = MkFix (MkAnnotT (MkAdaptorAdj adp, a))

------------------------------------------------------------

-- Abilities
data AbF :: Transformer -> * -> * where
  MkAb :: TFix t AbModF -> TFix t InterfaceMapF -> AbF t r                        -- interface-id  ->  list of ty arg's
deriving instance (Show (TFix t AbModF),
                   Show (TFix t InterfaceMapF),
                   Show r, Show (TFix t AbF)) => Show (AbF t r)
deriving instance (Eq (TFix t AbModF),
                   Eq (TFix t InterfaceMapF),
                   Eq r, Eq (TFix t AbF)) => Eq (AbF t r)
type Ab a = AnnotTFix a AbF
pattern Ab abMod itfMap a = MkFix (MkAnnotT (MkAb abMod itfMap, a))

-- Ability modes
data AbModF :: Transformer -> * -> * where
  MkEmpAb :: AbModF t r                                                     -- empty            (closed ability)
  MkAbVar :: NotDesugared (t Identity ()) => Identifier -> AbModF t r               -- non-desugared effect variable
  MkAbRVar :: Identifier -> AbModF (AnnotT Desugared)  r                            -- rigid eff var    (open ability)
  MkAbFVar :: Identifier -> AbModF (AnnotT Desugared)  r                            -- flexible eff var (open ability)
deriving instance (Show r, Show (TFix t AbModF)) => Show (AbModF t r)
deriving instance (Eq r, Eq (TFix t AbModF)) => Eq (AbModF t r)
type AbMod a = AnnotTFix a AbModF
pattern EmpAb a = MkFix (MkAnnotT (MkEmpAb, a))
pattern AbVar x a = MkFix (MkAnnotT (MkAbVar x, a))
pattern AbRVar x a = MkFix (MkAnnotT (MkAbRVar x, a))
pattern AbFVar x a = MkFix (MkAnnotT (MkAbFVar x, a))

data TypeArgF :: Transformer -> * -> * where
  MkVArg :: TFix t ValueTypeF -> TypeArgF t r
  MkEArg :: TFix t AbF   -> TypeArgF t r
deriving instance (Show (TFix t ValueTypeF),
                   Show (TFix t AbF),
                   Show r, Show (TFix t TypeArgF)) => Show (TypeArgF t r)
deriving instance (Eq (TFix t ValueTypeF),
                   Eq (TFix t AbF),
                   Eq r, Eq (TFix t TypeArgF)) => Eq (TypeArgF t r)
type TypeArg a = AnnotTFix a TypeArgF
pattern VArg ty a = MkFix (MkAnnotT (MkVArg ty, a))
pattern EArg ab a = MkFix (MkAnnotT (MkEArg ab, a))

-- TODO: LC: Make distinction between MkAdp and MkCompilableAdp on
-- type-level (GADT)
data AdaptorF :: Transformer -> * -> * where
  MkRawAdp :: Identifier -> Identifier -> [Identifier] -> [Identifier] -> AdaptorF (AnnotT Raw) r           -- e.g. I(s y x -> y x) (s is first arg, [y x] is second arg, [y x] is third arg)
  MkAdp :: Identifier -> Maybe Int -> [Int] -> AdaptorF t r                         -- adapt an interface `x` in an ability from right to left according to `ns` and (possibly - according to Maybe) attach all instances from `m` on
  MkCompilableAdp :: Identifier -> Int -> [Int] -> AdaptorF t r                     -- adapt an interface `x` in an ability that has exactly `n` instances of it from right to left according to `ns`
deriving instance (Show r, Show (TFix t AdaptorF)) => Show (AdaptorF t r)
deriving instance (Eq r, Eq (TFix t AdaptorF)) => Eq (AdaptorF t r)

type Adaptor a = AnnotTFix a AdaptorF

pattern RawAdp x liat left right a = MkFix (MkAnnotT (MkRawAdp x liat left right, a))
pattern Adp x mm ns a = MkFix (MkAnnotT (MkAdp x mm ns, a))
pattern CompilableAdp x m ns a = MkFix (MkAnnotT (MkCompilableAdp x m ns, a))

desugaredStrTy :: Desugared -> ValueType Desugared
desugaredStrTy a = DTTy "List" [VArg (CharTy a) a] a

getCmds :: Interface t -> [Cmd t]
getCmds (MkInterface _ _ xs _) = xs

collectINames :: [Interface t] -> [Identifier]
collectINames = map (\case (MkInterface itf _ _ _) -> itf)

getCtrs :: DataT t -> [Ctr t]
getCtrs (DT _ _ xs _) = xs

collectDTNames :: [DataT t] -> [Identifier]
collectDTNames = map (\case (DT dt _ _ _) -> dt)

-- Convert ability to a list of interface names and effect variables
{-
abToList :: Ab a -> [Identifier]
abToList MkEmpAb = []
abToList (MkAbVar id) = [id]
abToList MkOpenAb = []
abToList (MkAbPlus ab id _) = id : abToList ab

-- Substitute the ability for the distinguished effect variable in the type.
substOpenAb :: Ab a -> ValueType a -> ValueType a
substOpenAb ab (MkDTTy id abs xs) =
  MkDTTy id (map (substOpenAbAb ab) abs) (map (substOpenAb ab) xs)
substOpenAb ab (MkSCTy cty) = MkSCTy $ substOpenAbCompType ab cty
substOpenAb _ ty = ty

substOpenAbAb :: Ab a -> Ab a -> Ab a
substOpenAbAb ab MkEmpAb = MkEmpAb
substOpenAbAb ab MkOpenAb = ab
substOpenAbAb ab (MkAbVar x) = MkAbVar x
substOpenAbAb ab (MkAbPlus ab' x ts) =
  MkAbPlus (substOpenAbAb ab' ab) x (map (substOpenAb ab) ts)

substOpenAbAdj :: Ab a -> Adj a -> Adj a
substOpenAbAdj ab MkIdAdj = MkIdAdj
substOpenAbAdj ab (MkAdjPlus adj itf xs) =
  MkAdjPlus (substOpenAbAdj ab adj) itf (map (substOpenAb ab) xs)

substOpenAbCompType :: Ab a -> CompType a -> CompType a
substOpenAbCompType ab (MkCompType ps q) =
  MkCompType (map (substOpenAbPort ab) ps) (substOpenAbPeg ab q)

substOpenAbPeg :: Ab a -> Peg a -> Peg a
substOpenAbPeg ab (MkPeg ab' ty) =
  MkPeg (substOpenAbAb ab ab') (substOpenAb ab ty)

substOpenAbPort :: Ab a -> Port a -> Port a
substOpenAbPort ab (MkPort adj ty) =
  MkPort (substOpenAbAdj ab adj) (substOpenAb ab ty)
-}

getOpName :: Operator t -> Identifier
getOpName (Mono x _) = x
getOpName (Poly x _) = x
getOpName (CmdIdentifier x _) = x

-- transform type variable (+ its kind) to a raw tye variable argument
-- (use during refinement of itf maps)
tyVar2rawTyVarArg :: (Identifier, Kind) -> TypeArg Raw
tyVar2rawTyVarArg (id, VT) = VArg (TVar id (Raw Generated)) (Raw Generated)
tyVar2rawTyVarArg (id, ET) = EArg (liftAbMod (AbVar id (Raw Generated)))
                                  (Raw Generated)

-- transform type variable (+ its kind) to a rigid tye variable argument
-- (prepare for later unification)
tyVar2rigTyVarArg :: (Identifier, Kind) -> TypeArg Desugared
tyVar2rigTyVarArg (id, VT) = VArg (RTVar id (Desugared Generated))
                                  (Desugared Generated)
tyVar2rigTyVarArg (id, ET) = EArg (liftAbMod (AbRVar id
                                                     (Desugared Generated)))
                                  (Desugared Generated)

liftAbMod :: AbMod t -> Ab t
liftAbMod abMod = Ab abMod (InterfaceMap M.empty (getAnn abMod)) (getAnn abMod)

-- Only to be applied to identifiers representing rigid or flexible
-- metavariables (type or effect).
trimVar :: Identifier -> Identifier
trimVar = takeWhile (/= '$')

{- Operations on interface maps -}

-- For each interface, the instances are concatenated
-- e.g. [State Bool, State Int] + [State String, State Char] =
-- [State Bool, State Int, State String, State Char]
plusInterfaceMap :: InterfaceMap t -> InterfaceMap t -> InterfaceMap t
plusInterfaceMap (InterfaceMap m a) (InterfaceMap m' _) = foldl plusInterfaceMap' (InterfaceMap m a) (M.toList m')
  where plusInterfaceMap' :: InterfaceMap t -> (Identifier, Bwd [TypeArg t]) -> InterfaceMap t
        plusInterfaceMap' (InterfaceMap m'' a'') (x, instants) =
          if M.member x m'' then InterfaceMap (M.adjust (\instants' -> instants' <>< bwd2fwd instants) x m'') a''
                                                                       else InterfaceMap (M.insert x instants m'') a''

-- eg. [State Bool,State Int] + State Char = [State Bool,State Int,State Char]
addInstanceToInterfaceMap :: InterfaceMap Raw -> (Identifier, [TypeArg Raw]) -> InterfaceMap Raw
addInstanceToInterfaceMap (InterfaceMap m a) (x, args) =
  if M.member x m then InterfaceMap (M.adjust (:< args) x m) a
  else InterfaceMap (M.insert x (BEmp :< args) m) a

-- Given m1 and m2, return
-- 1) All interfaces that occur in m1 *and* m2
-- 2) Of those interface, take only the longest suffix of common length,
--    with instances from m1
intersectInterfaceMap :: InterfaceMap t -> InterfaceMap t -> InterfaceMap t
intersectInterfaceMap (InterfaceMap m1 a) (InterfaceMap m2 _) = InterfaceMap m'' a
  where m'  = M.intersectionWith (\args args' -> takeBwd (min (length args) (length args')) args) m1 m2
        m'' = M.filter (not . null) m'

-- Given m1 and m2, cut off entry suffixes of m1 of length determined by m2's
-- entries' lengths
cutInterfaceMapSuffix :: InterfaceMap t -> InterfaceMap t -> InterfaceMap t
cutInterfaceMapSuffix (InterfaceMap m1 a) (InterfaceMap m2 _) = InterfaceMap m'' a
  where m' = M.differenceWith (\args args' -> Just $ dropBwd (length args') args) m1 m2
        m'' = M.filter (not . null) m'

-- NOTE (Varun): This was dead code.
-- stripInactiveOffInterfaceMap :: InterfaceMap t -> InterfaceMap t
-- stripInactiveOffInterfaceMap (InterfaceMap m a) = InterfaceMap m' a
--   where m' = M.map (\case BEmp -> error "invariant broken"
--                           (_ :< x) -> BEmp :< x) m

isInterfaceMapSuffixOf :: Eq t => InterfaceMap t -> InterfaceMap t -> Bool
isInterfaceMapSuffixOf m1 m2 = (m2 `cutInterfaceMapSuffix` m1) `plusInterfaceMap` m1 == m2

emptyInterfaceMap :: t -> InterfaceMap t
emptyInterfaceMap = InterfaceMap M.empty

isInterfaceMapEmpty :: InterfaceMap t -> Bool
isInterfaceMapEmpty (InterfaceMap m _) = M.null m

-- Normal form of lists of adjustments
-- M.Map Identifier (Bwd [TypeArg Desugared]:  I -> Enrichments for I (instances which are
--                                   handled here)
-- M.Map Identifier (Renaming, Int):         I -> Total renaming for I, number of enrichments for I
adjsNormalForm :: [Adjustment Desugared] ->
                  (M.Map Identifier (Bwd [TypeArg Desugared]), M.Map Identifier Renaming)
adjsNormalForm = foldl (flip addAdjNormalForm) (M.empty, M.empty)

addAdjNormalForm :: Adjustment Desugared ->
  (M.Map Identifier (Bwd [TypeArg Desugared]), M.Map Identifier Renaming) ->
  (M.Map Identifier (Bwd [TypeArg Desugared]), M.Map Identifier Renaming)
addAdjNormalForm (ConsAdj x ts a) (insts, adps) =
  ( adjustWithDefault (:< ts) x BEmp insts
  , adjustWithDefault (\(rs, r) -> renToNormalForm (0 : map (+ 1) rs, r + 1)) x renIdentifier adps
  )
addAdjNormalForm (AdaptorAdj adp@(CompilableAdp x m ns _) a) (insts, adps) =
  ( insts
  , adjustWithDefault (renToNormalForm . renCompose (adpToRen adp)) x renIdentifier adps
  )
-- TODO: LC: double-check that the last line is correct

-- helpers

adjustWithDefault :: Ord k => (a -> a) -> k -> a -> M.Map k a -> M.Map k a
adjustWithDefault f k def = M.alter (Just . f . fromMaybe def) k

adpToRen :: Adaptor Desugared -> Renaming
adpToRen (CompilableAdp x m ns _) = (reverse ns, m)
