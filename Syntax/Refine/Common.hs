-- Definitions used during refinement phase
module Syntax.Refine.Common where

import Control.Monad
import Control.Monad.Except
import Control.Monad.State
import Data.Functor.Identity

import Data.List
import Data.Maybe
import qualified Data.Map.Strict as M
import qualified Data.Set as S

import Syntax

type Refine = ExceptT String (State RState)

type TVarMap = M.Map Identifier (ValueType Raw)
type EVarSet = S.Set Identifier

-- generic object-int pair
type IPair = (Identifier, Int)
-- data type id is mapped to rigid data type (RDT) variables (for polymorphic data types)
type DataTypeMap = M.Map Identifier [(Identifier, Kind)]                      -- dt-id     -> [ty-vars]
type IFMap = M.Map Identifier [(Identifier, Kind)]                      -- itf-id    -> [ty-vars]
type IFAliasesMap = M.Map Identifier ([(Identifier, Kind)], InterfaceMap Raw) -- itf-al-id -> ([ty-vars], itf's -> itf-instant's)

data TopLevelCtxt = Interface | InterfaceAlias | Datatype | Handler
  deriving (Show, Eq)

data RState = MkRState { interfaces :: IFMap
                       , interfaceAliases :: IFAliasesMap
                       , datatypes :: DataTypeMap
                       , handlers :: [IPair]              -- handler Id -> # of arguments
                       , ctrs :: [IPair]                  -- constructor Id -> # of arguments
                       , cmds :: [IPair]                  -- command Id -> # of arguments
                       , tmap :: TVarMap                  -- type var Id ->   ValueType Raw     val ty vars of current context
                       , evmap :: EVarSet                 -- effect var Id                  eff ty vars of current context
                       , tlctxt :: Maybe TopLevelCtxt }

getRState :: Refine RState
getRState = get

putRState :: RState -> Refine ()
putRState = put

putRInterfaces :: IFMap -> Refine ()
putRInterfaces xs = do
  s <- getRState
  putRState $ s { interfaces = xs }

getRInterfaces :: Refine IFMap
getRInterfaces = interfaces <$> getRState

putRInterfaceAliases :: IFAliasesMap -> Refine ()
putRInterfaceAliases xs = do
  s <- getRState
  putRState $ s {interfaceAliases = xs }

getRInterfaceAliases :: Refine IFAliasesMap
getRInterfaceAliases = interfaceAliases <$> getRState

putRDTs :: DataTypeMap -> Refine ()
putRDTs m = do s <- getRState
               putRState $ s { datatypes = m }

-- get rigid data types
getRDTs :: Refine DataTypeMap
getRDTs = datatypes <$> getRState

putRCtrs :: [IPair] -> Refine ()
putRCtrs xs = do s <- getRState
                 putRState $ s { ctrs = xs }

getRCtrs :: Refine [IPair]
getRCtrs = ctrs <$> getRState

putRCmds :: [IPair] -> Refine ()
putRCmds xs = do s <- getRState
                 putRState $ s { cmds = xs }

getRCmds :: Refine [IPair]
getRCmds = cmds <$> getRState

putRMHs :: [IPair] -> Refine ()
putRMHs xs = do s <- getRState
                putRState $ s { handlers = xs }

getRMHs :: Refine [IPair]
getRMHs = handlers <$> getRState

putTMap :: TVarMap -> Refine ()
putTMap m = do s <- getRState
               putRState $ s { tmap = m }

getTMap :: Refine TVarMap
getTMap = tmap <$> getRState

putEVSet :: EVarSet -> Refine ()
putEVSet m = do s <- getRState
                putRState $ s { evmap = m }

getEVSet :: Refine EVarSet
getEVSet = evmap <$> getRState

getTopLevelCtxt :: Refine (Maybe TopLevelCtxt)
getTopLevelCtxt = tlctxt <$> getRState

putTopLevelCtxt :: TopLevelCtxt -> Refine ()
putTopLevelCtxt ctxt = do s <- getRState
                          putRState $ s { tlctxt = Just ctxt }

{- Helper functions -}

isHeaderContext :: Maybe TopLevelCtxt -> Bool
isHeaderContext (Just Handler) = True
isHeaderContext _              = False

-- Check if ids are unique, if not throw error using the function "f"
checkUniqueIds :: (HasIdentifier a, HasSource a) => [a] -> (Identifier -> Source -> String) ->
                  Refine ()
checkUniqueIds xs f =
  let (_, mErr) = foldl (\(ys, mErr) x -> if isNothing mErr
                                          then let ident = getIdentifier x in
                                                 if ident `elem` ys
                                                 then ([], Just $ f ident (getSource x))
                                                 else (ident : ys, Nothing)
                                          else ([], mErr))
                        ([], Nothing) xs
  in forM_ mErr throwError
