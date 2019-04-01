{-# LANGUAGE TupleSections #-}

-- Making implicit [£] explicit in data type, interface and interface alias
-- definitions
module Syntax.Refine.ConcretiseEps (concretiseEps, concretiseEpsArg) where

import Control.Monad
import Control.Monad.Except
import Control.Monad.State
import Data.Functor.Identity

import Data.List
import qualified Data.Map.Strict as M
import qualified Data.Set as S

import BwdFwd
import Syntax
import qualified Syntax.AbilityMode as AbilityMode

-- | Node container for the graph algorithm
data Node
  = DtNode (DataType Raw)
  | InterfaceNode (Interface Raw)
  | InterfaceAlNode (InterfaceAlias Raw)
  deriving (Show, Eq)

-- | Used as a result of inspecting a node on whether it has an
-- (implicit/explicit) [£]
data HasEps
  = HasEps             -- ^ "Yes" with certainty
  | HasEpsIfAny [Node] -- ^ "Yes" if any of the given nodes (definitions) have
                       --   implicit [£]
                       --   (n.b. hasNoEps = HasEpsIfAny [] corresponds to "No")
  deriving (Show, Eq)

hasNoEps :: HasEps
hasNoEps = HasEpsIfAny []

-- Given data type, interface and interface alias def's, determine which of them
-- carry an implicit or explicit [£] eff var. As the def's may depend on each
-- other, we consider each def. a node and model the dependencies as a
-- dependency graph.
-- A node will be decided either positive (i.e. carries [£]) or
-- negative (i.e. no [£]). Whenever a node reaches a positive one, it is also
-- decided positive (i.e. any contained subtype requiring [£] induces
-- [£] for the parent).
-- Finally, all definitions that are decided to have [£], but do not yet
-- explicitly have it, are added an additional [£] eff var.
concretiseEps :: [DataType Raw] -> [Interface Raw] -> [InterfaceAlias Raw] -> ([DataType Raw], [Interface Raw], [InterfaceAlias Raw])
concretiseEps dts itfs itfAls =
  let posNodes = decideGraph (nodes, [], [])
      posDts    = [getIdentifier x | DtNode x    <- posNodes]
      posInterfaces   = [getIdentifier x | InterfaceNode x   <- posNodes]
      posInterfaceAls = [getIdentifier x | InterfaceAlNode x <- posNodes] in
  (map (concretiseEpsInDataType posDts) dts,
   map (concretiseEpsInInterface   posInterfaces) itfs,
   map (concretiseEpsInInterfaceAl posInterfaceAls) itfAls)
  where

  nodes :: [Node]
  nodes = map DtNode dts ++ map InterfaceNode itfs ++ map InterfaceAlNode itfAls

  resolveDataId :: Identifier -> Maybe Node
  resolveDataId x = case [DtNode d | DtNode d <- nodes, getIdentifier d == x] of
                      [x] -> Just x
                      _   -> Nothing
  -- TODO: LC: Use Map datastructure

  resolveInterfaceId :: Identifier -> Maybe Node
  resolveInterfaceId x = case ([i | InterfaceNode i <- nodes, getIdentifier i == x],
                         [i | InterfaceAlNode i <- nodes, getIdentifier i == x]) of
                     ([i], []) -> Just $ InterfaceNode i
                     ([], [i]) -> Just $ InterfaceAlNode i
                     _ -> Nothing

  -- Given graph (undecided-nodes, positive-nodes, negative-nodes), decide
  -- subgraphs as long as there are unvisited nodes. Finally (base case),
  -- return positive nodes.
  decideGraph :: ([Node], [Node], [Node]) -> [Node]
  decideGraph ([],   pos, _  ) = pos
  decideGraph (x:xr, pos, neg) = decideGraph $ runIdentity $ execStateT (decideSubgraph x) (xr, pos, neg)

  -- Given graph (passed as state, same as for decideGraph) and a starting
  -- node x (already excluded from the graph), visit the whole subgraph
  -- reachable from x and thereby decide each node.
  -- To avoid cycles, x must always be excluded from graph.
  -- Method: 1) Try to decide x on its own. Either:
  --            (1), (2) Already decided
  --            (3), (4) Decidable without dependencies
  --         2) If x's decision is dependent on neighbours' ones, visit all
  --            and recursively decide them, too. Either:
  --            (5)(i)  Some neighbour y is decided pos.  => x is pos.
  --            (5)(ii) All neighbours y are decided neg. => x is neg.
  decideSubgraph :: Node -> State ([Node], [Node], [Node]) Bool
  decideSubgraph x = do
    (xs, pos, neg) <- get
    if        x `elem` pos then return True      -- (1)
    else if   x `elem` neg then return False     -- (2)
    else case hasEpsNode x of
      HasEps          -> do put (xs, x:pos, neg) -- (3)
                            return True
      HasEpsIfAny nodes ->
        let neighbours = nub nodes `intersect` (xs ++ pos ++ neg) in
        do dec <- foldl (\dec y -> do -- Exclude neighbour from graph
                                      (xs', pos', neg') <- get
                                      put (xs' \\ [y], pos', neg')
                                      d  <- dec
                                      d' <- decideSubgraph y
                                      -- Once pos. y found, result stays pos.
                                      return $ d || d')
                        (return False)           -- (4) (no neighbours)
                        neighbours
           (xs', pos', neg') <- get
           if dec then put (xs', x:pos', neg')   -- (5)(i)
                  else put (xs', pos', x:neg')   -- (5)(ii)
           return dec

  {- hasEpsX functions examine an instance of X and determine whether it
     1) has an [£] for sure or
     2) has an [£] depending on other definitions

     The tvs parameter hold the locally introduced value type variables. It
     serves the following purpose: If an identifier is encountered, we cannot be
     sure if it was correctly determined as either data type or local type
     variable. This is the exact same issue to deal with as in refineValueType,
     now in hasEpsValueType -}

  hasEpsNode :: Node -> HasEps
  hasEpsNode node = case node of (DtNode dt) -> hasEpsDataType dt
                                 (InterfaceNode itf) -> hasEpsInterface itf
                                 (InterfaceAlNode itfAl) -> hasEpsInterfaceAl itfAl

  hasEpsDataType :: DataType Raw -> HasEps
  hasEpsDataType (MkDataType _ ps ctrs a) = if ("£", ET) `elem` ps then HasEps
                                 else let tvs = [x | (x, VT) <- ps] in
                                      anyHasEps (map (hasEpsCtr tvs) ctrs)

  hasEpsInterface :: Interface Raw -> HasEps
  hasEpsInterface (MkInterface _ ps cmds a) = if ("£", ET) `elem` ps then HasEps
                                else let tvs = [x | (x, VT) <- ps] in
                                     anyHasEps (map (hasEpsCmd tvs) cmds)

  hasEpsInterfaceAl :: InterfaceAlias Raw -> HasEps
  hasEpsInterfaceAl (MkInterfaceAlias _ ps itfMap a) = if ("£", ET) `elem` ps then HasEps
                                         else let tvs = [x | (x, VT) <- ps] in
                                              hasEpsInterfaceMap tvs itfMap

  hasEpsCmd :: [Identifier] -> Cmd Raw -> HasEps
  hasEpsCmd tvs (Cmd _ ps ts t a) = let tvs' = tvs ++ [x | (x, VT) <- ps] in
                                    anyHasEps $ map (hasEpsValueType tvs') ts ++ [hasEpsValueType tvs' t]

  hasEpsCtr :: [Identifier] -> Ctr Raw -> HasEps
  hasEpsCtr tvs (Ctr _ ts a) = anyHasEps (map (hasEpsValueType tvs) ts)

  hasEpsValueType :: [Identifier] -> ValueType Raw -> HasEps
  hasEpsValueType tvs (DTTy x ts a) =
    if x `elem` dtIds then hasEpsDTTy tvs x ts                   -- indeed data type
                      else anyHasEps $ map (hasEpsTypeArg tvs) ts  -- ... or not (but type var)
    where dtIds = [getIdentifier d | DtNode d <- nodes]
  hasEpsValueType tvs (SCTy ty a)   = hasEpsCompType tvs ty
  hasEpsValueType tvs (TVar x a)    = if x `elem` tvs then hasNoEps      -- indeed type variable
                                                  else hasEpsDTTy tvs x [] -- ... or not (but data type)
  hasEpsValueType tvs (StringTy _)  = hasNoEps
  hasEpsValueType tvs (IntTy _)     = hasNoEps
  hasEpsValueType tvs (CharTy _)    = hasNoEps

  hasEpsDTTy :: [Identifier] -> Identifier -> [TypeArg Raw] -> HasEps
  hasEpsDTTy tvs x ts =
    -- An datatype x gives only rise to adding an eps if the number of ty
    -- args are exactly as required by x. Thus, if x has an additional
    -- implicit eps, it should be given as an additional parameter here, too
    case resolveDataId x of
      Just x' -> let
        dtHE   = [HasEpsIfAny [x'] | isDtWithNArgs x' (length ts)]
        argsHE = map (hasEpsTypeArg tvs) ts
        in anyHasEps (dtHE ++ argsHE)
      Nothing -> hasNoEps
    where isDtWithNArgs :: Node -> Int -> Bool
          isDtWithNArgs (DtNode (MkDataType _ ps _ _)) n = length ps == n


  hasEpsCompType :: [Identifier] -> CompType Raw -> HasEps
  hasEpsCompType tvs (CompType ports peg a) = anyHasEps $ map (hasEpsPort tvs) ports ++ [hasEpsPeg tvs peg]

  hasEpsPort :: [Identifier] -> Port Raw -> HasEps
  hasEpsPort tvs (Port adjs ty a) = anyHasEps [anyHasEps (map (hasEpsAdj tvs) adjs), hasEpsValueType tvs ty]

  hasEpsAdj :: [Identifier] -> Adjustment Raw -> HasEps
  hasEpsAdj tvs (ConsAdj x ts a) = anyHasEps (map (hasEpsTypeArg tvs) ts)
  hasEpsAdj _ (AdaptorAdj _ _) = hasNoEps

  hasEpsPeg :: [Identifier] -> Peg Raw -> HasEps
  hasEpsPeg tvs (Peg ab ty a) = anyHasEps [hasEpsAb tvs ab, hasEpsValueType tvs ty]

  hasEpsAb :: [Identifier] -> Ability Raw -> HasEps
  hasEpsAb tvs (MkAbility v m a) = anyHasEps [hasEpsAbMod tvs v, hasEpsInterfaceMap tvs m]

  hasEpsInterfaceMap :: [Identifier] -> InterfaceMap Raw -> HasEps
  hasEpsInterfaceMap tvs mp@(InterfaceMap m _) =
    let -- An interface i gives only rise to adding an eps if the number of ty
        -- args are exactly as required by i. Thus, if i has an additional
        -- implicit eps, it should be given as an additional parameter here, too
        itfsHE = map hasEpsInst (flattenInterfaceMap mp)
        argsHE = (map (hasEpsTypeArg tvs) . concat . concatMap bwd2fwd . M.elems) m
    in anyHasEps (itfsHE ++ argsHE)
    where flattenInterfaceMap :: InterfaceMap t -> [(Identifier, [TypeArg t])]
          flattenInterfaceMap (InterfaceMap m _) = concatMap (\(i, insts) -> map (i,) (bwd2fwd insts)) (M.toList m)

          hasEpsInst :: (Identifier, [TypeArg Raw]) -> HasEps
          hasEpsInst (i, inst) = case resolveInterfaceId i of
            Just x -> if isInterfaceWithNArgs x (length inst) then HasEpsIfAny [x] else hasNoEps
            _ -> hasNoEps

          isInterfaceWithNArgs :: Node -> Int -> Bool
          isInterfaceWithNArgs (InterfaceNode (MkInterface _ ps _ _))        n = length ps == n
          isInterfaceWithNArgs (InterfaceAlNode (MkInterfaceAlias _ ps _ _)) n = length ps == n

  hasEpsAbMod :: [Identifier] -> AbilityMode Raw -> HasEps
  hasEpsAbMod tvs (AbilityMode.Empty _)     = hasNoEps
  hasEpsAbMod tvs (AbilityMode.Var "£" _) = HasEps
  hasEpsAbMod tvs (AbilityMode.Var _ _)   = hasNoEps

  hasEpsTypeArg :: [Identifier] -> TypeArg Raw -> HasEps
  hasEpsTypeArg tvs (VArg t _)  = hasEpsValueType tvs t
  hasEpsTypeArg tvs (EArg ab _) = hasEpsAb tvs ab

concretiseEpsInDataType :: [Identifier] -> DataType Raw -> DataType Raw
concretiseEpsInDataType posIds (MkDataType dt ps ctrs a) = MkDataType dt ps' ctrs a where
  ps' = if ("£", ET) `notElem` ps && dt `elem` posIds then ps ++ [("£", ET)] else ps

concretiseEpsInInterface :: [Identifier] -> Interface Raw -> Interface Raw
concretiseEpsInInterface posIds (MkInterface itf ps cmds a) = MkInterface itf ps' cmds a where
  ps' = if ("£", ET) `notElem` ps && itf `elem` posIds then ps ++ [("£", ET)] else ps

concretiseEpsInInterfaceAl :: [Identifier] -> InterfaceAlias Raw -> InterfaceAlias Raw
concretiseEpsInInterfaceAl posIds (MkInterfaceAlias itfAl ps itfMap a) =
  MkInterfaceAlias itfAl ps' itfMap a
  where
    ps' = if ("£", ET) `notElem` ps && itfAl `elem` posIds
          then ps ++ [("£", ET)]
          else ps

{- This function adds an implicit [£|] *argument* if the type signature
   requires it. -}

concretiseEpsArg :: [(Identifier, Kind)] -> [TypeArg Raw] -> Raw -> [TypeArg Raw]
concretiseEpsArg ps ts a = if length ps == length ts + 1 &&
                              (snd (ps !! length ts) == ET)
                           then ts ++ [EArg (MkAbility (AbilityMode.Var "£" a) (InterfaceMap M.empty a) a) a]
                           else ts

{- Helper functions -}

-- A variant of the any-operator for HasEps results
anyHasEps :: [HasEps] -> HasEps
anyHasEps xs = if HasEps `elem` xs then HasEps
               else HasEpsIfAny (concat [ids | HasEpsIfAny ids <- xs])
