-- Unification implementation inspired heavily by Adam Gundry's thesis.
module Unification where

import qualified Data.Map as M
import qualified Data.Set as S

import Control.Monad.Except

import BwdFwd
import FreshNames
import Syntax
import TypeCheckCommon
import Debug

data Extension = Restore | Replace Suffix

restore :: Contextual Extension
restore = return Restore

replace :: Suffix -> Contextual Extension
replace = return . Replace

-- 1) Go through context until the first FlexMVar x:=d appears.
-- 2) Run "f" on "x:=d", resulting in either "Restore" or "Replace-by-ext"
onTop :: (Identifier -> Decl -> Contextual Extension) -> Contextual ()
onTop f = popEntry >>= focus
  where focus :: Entry -> Contextual ()
        focus e@(FlexMVar x d) =
          do m <- f x d
             case m of
               Replace ext -> modify (<>< entrify ext)
               Restore -> modify (:< e)
        focus e = onTop f >> modify (:< e)

-- unify 2 val tys in current context
unify :: ValueType Desugared -> ValueType Desugared -> Contextual ()                    -- corresponding rule in Gundry's thesis:
unify t0 t1 = do logBeginUnify t0 t1
                 unify' t0 t1
                 logEndUnify t0 t1
  where
  unify' (DTTy dt0 ts0 _) (DTTy dt1 ts1 _)                                      -- decompose (modified)
    | dt0 == dt1 && eqLens ts0 ts1 =
      zipWithM_ unifyTypeArg ts0 ts1
  unify' v1@(DTTy dt0 ts0 _) v2@(DTTy dt1 ts1 _)                                -- decompose fails
    | not $ eqLens ts0 ts1 =
    throwError $ errorUnifDiffNumberArgs v1 v2
  unify' (SCTy cty0 _)   (SCTy cty1 _)        = unifyCompType cty0 cty1
  unify' (RTVar a _)     (RTVar b _) | a == b = return ()
  unify' (IntTy _)       (IntTy _)            = return ()
  unify' (CharTy _)      (CharTy _)           = return ()
  unify' fta@(FTVar a _) ftb@(FTVar b _)      = onTop $ \c d ->
    cmp (a == c) (b == c) d
    where cmp :: Bool -> Bool -> Decl -> Contextual Extension
          cmp True  True  _           = restore                                 -- idle
          cmp True  False Hole        = replace [(a, TyDefn ftb)]               -- define
          cmp False True  Hole        = replace [(b, TyDefn fta)]               -- define
          cmp True  False (TyDefn ty) = unify ty ftb >> restore                 -- subs
          cmp False True  (TyDefn ty) = unify fta ty >> restore                 -- subs
          cmp False False _           = unify fta ftb >> restore                -- skip-ty
          cmp _     _     (AbDefn _)  = error "unification invariant broken"
  unify' (FTVar x a)     ty                   = solve x a [] ty                 -- inst
  unify' ty              (FTVar y b)          = solve y b [] ty                 -- inst
  unify' t               s                    = throwError $ errorUnifTys t s

-- unify 2 eff tys in current context
unifyAb :: Ab Desugared -> Ab Desugared -> Contextual ()
unifyAb ab0@(Ab v0 m0 a) ab1@(Ab v1 m1 b) =
  do logBeginUnifyAb ab0 ab1
     -- expand abs by resolving all flexible variables
     ab0' <- expandAb ab0
     ab1' <- expandAb ab1
     -- then unify
     unifyAb' ab0' ab1'
     logEndUnifyAb ab0 ab1
  where unifyAb' :: Ab Desugared -> Ab Desugared -> Contextual ()
        -- Same eff ty vars leaves nothing to unify but instantiat's m0, m1
        unifyAb' ab0@(Ab v0 m1 _) ab1@(Ab v1 m2 _) | stripAnn v0 == stripAnn v1 =
          catchError (unifyInterfaceMap m1 m2) (unifyAbError ab0 ab1)
        -- Both eff ty vars are flexible
        unifyAb' (Ab (AbFVar x a') m1 a) (Ab (AbFVar y b') m2 b) =
          do -- For same occurrences of interfaces, their instantiat's must coincide
             unifyInterfaceMap (intersectInterfaceMap m1 m2) (intersectInterfaceMap m2 m1)
             v <- AbFVar <$> freshMVar "£" <*> pure (Desugared Generated)
             solveForEVar x a' [] (Ab v (m2 `cutInterfaceMapSuffix` m1) a)  -- TODO: LC: locations assigned correctly?
             solveForEVar y b' [] (Ab v (m1 `cutInterfaceMapSuffix` m2) b)
        -- One eff ty var is flexible, the other one either empty or rigid
        unifyAb' (Ab (AbFVar x a') m1 _) (Ab v m2 b)
          | isInterfaceMapEmpty (cutInterfaceMapSuffix m1 m2) =
            do unifyInterfaceMap (intersectInterfaceMap m1 m2) (intersectInterfaceMap m2 m1)
               solveForEVar x a' [] (Ab v (m2 `cutInterfaceMapSuffix` m1) b)   -- TODO: LC: locations assigned correctly?
        unifyAb' (Ab v m1 a) (Ab (AbFVar y b') m2 _)
          | isInterfaceMapEmpty (cutInterfaceMapSuffix m2 m1) =
            do unifyInterfaceMap (intersectInterfaceMap m1 m2) (intersectInterfaceMap m2 m1)
               solveForEVar y b' [] (Ab v (m1 `cutInterfaceMapSuffix` m2) a)   -- TODO: LC: locations assigned correctly?
        -- In any other case
        unifyAb' ab0 ab1 = throwError $ errorUnifAbs ab0 ab1

unifyTypeArg :: TypeArg Desugared -> TypeArg Desugared -> Contextual ()
unifyTypeArg (VArg t0 _) (VArg t1 _) = unify t0 t1
unifyTypeArg (EArg ab0 _) (EArg ab1 _) = unifyAb ab0 ab1
unifyTypeArg arg0 arg1 = throwError $ errorUnifTypeArgs arg0 arg1

unifyAbError :: Ab Desugared -> Ab Desugared -> String -> Contextual ()
unifyAbError ab0 ab1 _ = throwError $ errorUnifAbs ab0 ab1

-- Given two interface maps, check that each instantiation has a unifiable
-- counterpart in the other ability and unify.
unifyInterfaceMap :: InterfaceMap Desugared -> InterfaceMap Desugared -> Contextual ()
unifyInterfaceMap m0@(InterfaceMap m0' a) m1@(InterfaceMap m1' b) = do
  mapM_ (unifyInterfaceMap' m1) (M.toList m0')
  mapM_ (unifyInterfaceMap' m0) (M.toList m1')
  where unifyInterfaceMap' :: InterfaceMap Desugared -> (Identifier, Bwd [TypeArg Desugared]) -> Contextual ()
        unifyInterfaceMap' (InterfaceMap m _) (x, insts) = case M.lookup x m of
          Nothing -> throwError $ errorUnifInterfaceMaps m0 m1
          Just insts' -> if length insts /= length insts' then throwError $ errorUnifInterfaceMaps m0 m1
                         else zipWithM_ (zipWithM_ unifyTypeArg) (bwd2fwd insts) (bwd2fwd insts')

unifyCompType :: CompType Desugared -> CompType Desugared -> Contextual ()
unifyCompType (CompType xs p0 _) (CompType ys p1 _) =
  zipWithM_ unifyPort xs ys >> unifyPeg p0 p1

unifyPeg :: Peg Desugared -> Peg Desugared -> Contextual ()
unifyPeg (Peg ab0 ty0 _) (Peg ab1 ty1 _) = unifyAb ab0 ab1 >> unify ty0 ty1

-- Two ports unify if
-- 1) their adjustments coincide (first normalise both)
-- 2) their types unify
unifyPort :: Port Desugared -> Port Desugared -> Contextual ()
unifyPort (Port adjs1 ty1 _) (Port adjs2 ty2 _) =
  do let (insts1, adps1) = adjsNormalForm adjs1
     let (insts2, adps2) = adjsNormalForm adjs2
     unifyInterfaceMap (InterfaceMap insts1 (Desugared Generated))  -- TODO: LC: fix this
                 (InterfaceMap insts2 (Desugared Generated))
     if adps1 == adps2 then
       unify ty1 ty2
     else throwError "adaptors not the same"

-- unify a meta variable "x" with a type "ty"
solve :: Identifier -> Desugared -> Suffix -> ValueType Desugared -> Contextual ()
solve x a ext ty = do logBeginSolve x ext ty
                      solve'
                      logEndSolve x ext ty
  where
  solve' = onTop $ \y d -> do
    logSolveStep (x == y, S.member y (fmv ty), d)
    case (x == y, S.member y (fmv ty), d) of
      (_,     _,     TyDefn bty) -> modify (<>< entrify ext) >>                 -- inst-subs (val ty var)
                                    unify (subst bty y (FTVar x a)) (subst bty y ty) >>
                                    restore
      (_,     _,     AbDefn ab) ->  modify (<>< entrify ext) >>                 -- inst-subs (eff ty var)
                                    unify (substEVar ab y (FTVar x a)) (substEVar ab y ty) >>
                                    restore
      (True,  True,  Hole) -> throwError errorUnifSolveOccurCheck
      (True,  False, Hole) -> replace (ext ++ [(x, TyDefn ty)])                 -- inst-define
      (False, True,  Hole) -> solve x a ((y, d):ext) ty >> replace []           -- inst-depend
      (False, False, Hole) -> solve x a ext ty >> restore                       -- inst-skip-ty

solveForEVar :: Identifier -> Desugared -> Suffix -> Ab Desugared -> Contextual ()
solveForEVar x a ext ab = onTop $ \y d ->
  case (x == y, S.member y (fmvAb ab), d) of
    (_, _, AbDefn ab') ->
      let vab = Ab (AbFVar x a) (InterfaceMap M.empty a) a in
      modify (<>< entrify ext) >>
      unifyAb (substEVarAb ab' y vab) (substEVarAb ab' y ab) >>
      restore
    (True, True, Hole) -> throwError errorUnifSolveOccurCheck
    (True, False, Hole) -> replace (ext ++ [(x, AbDefn ab)])
    (False, True, _) -> solveForEVar x a ((y, d):ext) ab >> replace []
    (False, False, _) -> solveForEVar x a ext ab >> restore
    (_, _, TyDefn _) ->
      error "solveForEVar invariant broken: reached impossible case"

{- Substitute "ty" for "x" in X -}

subst :: ValueType Desugared -> Identifier -> ValueType Desugared -> ValueType Desugared
subst ty x (DTTy dt ts a) = DTTy dt (map (substTypeArg ty x) ts) a
subst ty x (SCTy cty a) = SCTy (substCompType ty x cty) a
subst ty x (FTVar y a) | x == y = ty
subst _ _ ty = ty

substAb :: ValueType Desugared -> Identifier -> Ab Desugared -> Ab Desugared
substAb ty x (Ab v (InterfaceMap m a') a) = Ab v (InterfaceMap m' a') a
  where m' = fmap (fmap (map (substTypeArg ty x))) m

substTypeArg :: ValueType Desugared -> Identifier -> TypeArg Desugared -> TypeArg Desugared
substTypeArg ty x (VArg t a) = VArg (subst ty x t) a
substTypeArg ty x (EArg ab a) = EArg (substAb ty x ab) a

substAdj :: ValueType Desugared -> Identifier -> Adjustment Desugared -> Adjustment Desugared
substAdj ty x (ConsAdj y ts a) = ConsAdj y (map (substTypeArg ty x) ts) a
substAdj ty x (AdaptorAdj adp a) = AdaptorAdj adp a

substCompType :: ValueType Desugared -> Identifier -> CompType Desugared -> CompType Desugared
substCompType ty x (CompType ps peg a) =
  CompType (map (substPort ty x) ps) (substPeg ty x peg) a

substPeg :: ValueType Desugared -> Identifier -> Peg Desugared -> Peg Desugared
substPeg ty x (Peg ab pty a) = Peg (substAb ty x ab) (subst ty x pty) a

substPort :: ValueType Desugared -> Identifier -> Port Desugared -> Port Desugared
substPort ty x (Port adjs pty a) = Port (map (substAdj ty x) adjs) (subst ty x pty) a

substEVar :: Ab Desugared -> Identifier -> ValueType Desugared -> ValueType Desugared
substEVar ab x (DTTy dt ts a) = DTTy dt (map (substEVarTypeArg ab x) ts) a
substEVar ab x (SCTy cty a) = SCTy (substEVarCompType ab x cty) a
substEVar _ _ ty = ty

-- substitute "ab" for "x" in AB
substEVarAb :: Ab Desugared -> Identifier -> Ab Desugared -> Ab Desugared
substEVarAb ab@(Ab v m' _) x (Ab (AbFVar y a) (InterfaceMap m ann') ann) | x == y =
  Ab v m'' ann
  where m'' = plusInterfaceMap m' (InterfaceMap (fmap (fmap (map (substEVarTypeArg ab x))) m) ann')
substEVarAb ab x (Ab v (InterfaceMap m a') a) = Ab v (InterfaceMap (M.map (fmap (map (substEVarTypeArg ab x))) m) a') a

substEVarTypeArg :: Ab Desugared -> Identifier -> TypeArg Desugared -> TypeArg Desugared
substEVarTypeArg ab x (VArg t a)  = VArg (substEVar ab x t) a
substEVarTypeArg ab x (EArg ab' a) = EArg (substEVarAb ab x ab') a

substEVarAdj :: Ab Desugared -> Identifier -> Adjustment Desugared -> Adjustment Desugared
substEVarAdj ab x (ConsAdj y ts a) = ConsAdj y (map (substEVarTypeArg ab x) ts) a
substEvarAdj ab x (AdaptorAdj adp a) = AdaptorAdj adp a

substEVarCompType :: Ab Desugared -> Identifier -> CompType Desugared -> CompType Desugared
substEVarCompType ab x (CompType ps peg a) =
  CompType (map (substEVarPort ab x) ps) (substEVarPeg ab x peg) a

substEVarPeg :: Ab Desugared -> Identifier -> Peg Desugared -> Peg Desugared
substEVarPeg ab' x (Peg ab pty a) =
  Peg (substEVarAb ab' x ab) (substEVar ab' x pty) a

substEVarPort :: Ab Desugared -> Identifier -> Port Desugared -> Port Desugared
substEVarPort ab x (Port adjs pty a) =
  Port (map (substEVarAdj ab x) adjs) (substEVar ab x pty) a

{- Helpers -}

eqLens :: [a] -> [a] -> Bool
eqLens xs ys = length xs == length ys
