{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE StandaloneDeriving #-}

module Syntax.Common
  (module Syntax.Common, Identity)
  where

import Data.Functor.Identity (Identity)
import Data.Kind (Constraint, Type)
import Data.Coerce (coerce)

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

instance HasSource a => HasSource (AnnotTFix a f) where
  getSource x = getSource (getAnn x)

-- NOTE (Varun): Erm, why is this changing things?
implicitNear :: HasSource a => a -> Source
implicitNear v = case getSource v of
  InCode (line, col) -> ImplicitNear (line, col)
  _                  -> Implicit

type Typeclass = Type -> Constraint

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

instance HasSource Raw where
  getSource = coerce

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

instance HasSource Refined where
  getSource = coerce

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

instance HasSource Desugared where
  getSource = coerce
