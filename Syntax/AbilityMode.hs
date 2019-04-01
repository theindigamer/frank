{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE PatternSynonyms #-}

module Syntax.AbilityMode
  ( AbilityModeF, AbilityMode
  , pattern Empty, pattern Var, pattern RigidVar, pattern FlexibleVar
  )
  where

import Syntax.Common

------------------------------------------------------------
-- *** Ability modes

-- | Ability modes
data AbilityModeF :: Transformer -> * -> * where
  -- | empty (closed ability)
  MkEmpAb :: AbilityModeF t r
  -- | non-desugared effect variable
  MkAbVar :: NotDesugared (t Identity ()) => Identifier -> AbilityModeF t r
  -- | rigid eff var    (open ability)
  MkAbRVar :: Identifier -> AbilityModeF (AnnotT Desugared)  r
  -- | flexible eff var (open ability)
  MkAbFVar :: Identifier -> AbilityModeF (AnnotT Desugared)  r

deriving instance (Show r, Show (TFix t AbilityModeF)) => Show (AbilityModeF t r)
deriving instance (Eq r, Eq (TFix t AbilityModeF)) => Eq (AbilityModeF t r)

type AbilityMode a = AnnotTFix a AbilityModeF

pattern Empty a = MkFix (MkAnnotT (MkEmpAb, a))
pattern Var x a = MkFix (MkAnnotT (MkAbVar x, a))
pattern RigidVar x a = MkFix (MkAnnotT (MkAbRVar x, a))
pattern FlexibleVar x a = MkFix (MkAnnotT (MkAbFVar x, a))
