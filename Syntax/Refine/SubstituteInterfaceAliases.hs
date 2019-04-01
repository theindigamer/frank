-- Recursively substitute an interface alias occurrence by its definition

module Syntax.Refine.SubstituteInterfaceAliases (substitInterfaceAls) where

import Control.Monad
import Control.Monad.Except
import Control.Monad.State
import Data.Functor.Identity

import Data.List
import qualified Data.Map.Strict as M
import qualified Data.Set as S

import BwdFwd
import Syntax
import Syntax.Refine.Common
import Syntax.Refine.ConcretiseEps
import Debug

-- Given an occurrence of interface instantiation x t_1 ... t_n:
-- 1) Implicit [£] are made explicit
-- 2) Determine whether it is an interface alias and if so, recursiv. substitute
substitInterfaceAls :: (Identifier, [TypeArg Raw]) -> Refine (InterfaceMap Raw)
substitInterfaceAls = substitInterfaceAls' [] where
  substitInterfaceAls' :: [Identifier] -> (Identifier, [TypeArg Raw]) -> Refine (InterfaceMap Raw)
  substitInterfaceAls' visited (x, ts) = do
    itfAls <- getRInterfaceAliases
    if x `notElem` visited then
      case M.lookup x itfAls of
        Nothing -> return $ InterfaceMap (M.singleton x (BEmp :< ts)) (Raw Generated) --TODO: LC: put meaningful annot here
        Just (ps, InterfaceMap m _) ->
--            1) interface x p_1 ... p_n     = [itf_i p_i1 ... p_ik, ...]
--         or 2) interface x p_1 ... p_n [£] = [itf_i p_i1 ... p_ik, ...]
--               and [£] has been explicitly added before
--                                if 2), set t_{n+1} := [£]
          do evset <- getEVSet
             ctx <- getTopLevelCtxt
             let ts' = if "£" `S.member` evset || isHeaderContext ctx
                       then concretiseEpsArg ps ts (Raw Implicit)
                       else ts
             checkArgs x (length ps) (length ts') (Raw Generated) -- TODO: LC: Fix annotation
             let subst = zip ps ts'
             -- replace   x ts
             --      by   [x_1 ts_1', ..., x_n ts_n']
             --           where ts_i' has been acted upon by subst
             m' <- mapM (mapM (mapM (substitInTypeArg subst))) m
             -- recursively replace itf als in   x_1, ..., x_n
             --                       yielding   [[x_11 x_11_ts, ...], ...]
             ms <- mapM (\(x', insts) -> mapM (\inst -> substitInterfaceAls' (x:visited) (x', inst)) insts) (M.toList m')
             let ms' = map (foldl plusInterfaceMap (emptyInterfaceMap (Raw Generated))) ms
             let m'' = foldl plusInterfaceMap (emptyInterfaceMap (Raw Generated)) ms'
             return m''
    else throwError $ errorRefInterfaceAlCycle x

type Subst = [((Identifier, Kind), TypeArg Raw)]

substLookupVT :: Subst -> Identifier -> Maybe (ValueType Raw)
substLookupVT subst x = case find (\((x', k), y) -> x' == x && k == VT) subst of
  Just (_, VArg ty a) -> Just ty
  _                    -> Nothing

substLookupET :: Subst -> Identifier -> Maybe (Ability Raw)
substLookupET subst x = case find (\((x', k), y) -> x' == x && k == ET) subst of
  Just (_, EArg ab a) -> Just ab
  _                    -> Nothing

substitInTypeArgs :: Subst -> (Identifier, [TypeArg Raw]) -> Refine (Identifier, [TypeArg Raw])
substitInTypeArgs subst (x, ts) = do
  ts' <- mapM (substitInTypeArg subst) ts
  return (x, ts')
-- Replace (x, VT/ET) by ty-arg
substitInTypeArg :: Subst -> TypeArg Raw -> Refine (TypeArg Raw)
substitInTypeArg subst (VArg ty a) = VArg <$> substitInValueType subst ty <*> pure a
substitInTypeArg subst (EArg ab a) = EArg <$> substitInAb subst ab <*> pure a

substitInValueType :: Subst -> ValueType Raw -> Refine (ValueType Raw)
substitInValueType subst (DTTy x ts a) = do
  dtm <- getRDTs
  tmap <- getTMap
  ctx <- getTopLevelCtxt
  let isTypeVar = not (M.member x dtm)
  case ( isTypeVar && null ts && (isHeaderContext ctx || M.member x tmap)
       , substLookupVT subst x
       ) of -- if so, then substitute
    (True, Just y) -> return y     -- TODO: LC: Right annotation assigned?
    _              -> do ts' <- mapM (substitInTypeArg subst) ts
                         return $ DTTy x ts' a
substitInValueType subst (SCTy ty a) = do
  cty <- substitInCompType subst ty
  return $ SCTy cty a
substitInValueType subst (TVar x a) =
  case substLookupVT subst x of
    Just y -> return y   -- TODO: LC: Right annotation assigned?
    _      -> return $ TVar x a
substitInValueType subst ty = return ty  -- MkStringTy, MkIntTy, MkCharTy

substitInCompType :: Subst -> CompType Raw -> Refine (CompType Raw)
substitInCompType subst (CompType ports peg a) = do
  ports' <- mapM (substitInPort subst) ports
  peg' <- substitInPeg subst peg
  return $ CompType ports' peg' a

substitInPort :: Subst -> Port Raw -> Refine (Port Raw)
substitInPort subst (Port adjs ty a) = do adjs' <- mapM (substitInAdj subst) adjs
                                          ty' <- substitInValueType subst ty
                                          return $ Port adjs' ty' a

substitInPeg :: Subst -> Peg Raw -> Refine (Peg Raw)
substitInPeg subst (Peg ab ty a) = do ab' <- substitInAb subst ab
                                      ty' <- substitInValueType subst ty
                                      return $ Peg ab' ty' a

substitInAb :: Subst -> Ability Raw -> Refine (Ability Raw)
substitInAb subst = return

substitInAdj :: Subst -> Adjustment Raw -> Refine (Adjustment Raw)
substitInAdj subst (ConsAdj x ts a) = do
  ts' <- mapM (substitInTypeArg subst) ts
  return $ ConsAdj x ts' a

substitInInterfaceMap :: Subst -> InterfaceMap Raw -> Refine (InterfaceMap Raw)
substitInInterfaceMap subst (InterfaceMap m a) = InterfaceMap <$> mapM (mapM (mapM (substitInTypeArg subst))) m <*> pure a

-- helpers

checkArgs :: Identifier -> Int -> Int -> Raw -> Refine ()
checkArgs x exp act a =
  when (exp /= act) $
    throwError $ errorRefNumberOfArguments x exp act a
