{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE PatternSynonyms #-}

module Syntax.Adaptor
  (AdaptorF, Adaptor, pattern Raw, pattern Adp, pattern Compilable)
  where

import Data.Kind (Type)

import Syntax.Common
  (Fix (MkFix), AnnotT (MkAnnotT), AnnotTFix, TFix, Identifier, Raw)

------------------------------------------------------------
-- *** Adaptors

-- TODO: LC: Make distinction between MkAdp and MkCompilableAdp on
-- type-level (GADT)
data AdaptorF :: ((* -> *) -> (* -> *)) -> * -> * where
 -- | e.g. I(s y x -> y x) (s is first arg, [y x] is second arg, [y x] is third arg)
  MkRawAdp
    :: Identifier
    -> Identifier
    -> [Identifier]
    -> [Identifier]
    -> AdaptorF (AnnotT Raw) r

  -- | Adapt an interface `x` in an ability from right to left according to `ns`
  -- and (possibly - according to Maybe) attach all instances from `m` on
  MkAdp :: Identifier -> Maybe Int -> [Int] -> AdaptorF t r

  -- | adapt an interface `x` in an ability that has exactly `n` instances of
  -- it from right to left according to `ns`
  MkCompilableAdp :: Identifier -> Int -> [Int] -> AdaptorF t r

deriving instance (Show r, Show (TFix t AdaptorF)) => Show (AdaptorF t r)
deriving instance (Eq r, Eq (TFix t AdaptorF)) => Eq (AdaptorF t r)

type Adaptor a = AnnotTFix a AdaptorF

pattern Raw x liat left right a = MkFix (MkAnnotT (MkRawAdp x liat left right, a))
pattern Adp x mm ns a = MkFix (MkAnnotT (MkAdp x mm ns, a))
pattern Compilable x m ns a = MkFix (MkAnnotT (MkCompilableAdp x m ns, a))
