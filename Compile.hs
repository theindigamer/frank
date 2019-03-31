{-# LANGUAGE ScopedTypeVariables #-}

-- Compile Frank to Shonky
module Compile where

import Control.Monad
import Control.Monad.Identity
import Control.Monad.State

import Data.List
import qualified Data.Map.Strict as M
import qualified Data.Set as S

import Syntax
import qualified Shonky.Syntax as S
import Shonky.Renaming

import Debug.Trace
import Debug

import BwdFwd

testShonky = unlines
  [ "evalstate(,get put):"
  , "evalstate(x,y) -> y,"
  , "evalstate(x,{'get() -> k}) -> evalstate(x,k(x)),"
  , "evalstate(x,{'put(y) -> k}) -> evalstate(y,k([]))"
  , "main():"
  , "main() -> evalstate([|hello|], 'put(['get(),[|world|]]);'get())"
  ]

type Compile = State CState

type InterfaceCmdMap = M.Map Identifier [Identifier]

data CState = MkCState { imap :: InterfaceCmdMap
                       , atoms :: S.Set String}

initCState :: CState
initCState = MkCState M.empty S.empty

getCState :: Compile CState
getCState = get

putCState :: CState -> Compile ()
putCState = put

getCCmds :: Identifier -> Compile [Identifier]
getCCmds itf = M.findWithDefault [] itf . imap <$> getCState

addAtom :: Identifier -> Compile ()
addAtom id = do s <- getCState
                putCState $ s { atoms = S.insert id (atoms s) }

isAtom :: Identifier -> Compile Bool
isAtom ident = S.member ident . atoms <$> getCState

compileToFile :: Program Desugared -> String -> IO ()
compileToFile p dst = writeFile (dst ++ ".uf") (show $ ppProgShonky $ compile p)

compile :: Program Desugared -> [S.Def S.Exp]
compile (MkProgram xs) = res
  where res = reverse $ evalState (compile' xs) st
        st = initialiseInterfaceMap initCState [i | InterfaceTerm i _ <- xs]

compile' :: [TopTerm Desugared] -> Compile [S.Def S.Exp]
compile' xs = concat <$> mapM compileTopTerm xs

initialiseInterfaceMap :: CState -> [Interface Desugared] -> CState
initialiseInterfaceMap st xs = st { imap = foldl f (imap st) xs }
  where f m (MkInterface id _ xs _) = foldl (ins id) m xs
        ins itf m (Cmd cmd _ _ _ _) =
          let xs = M.findWithDefault [] itf m in
          M.insert itf (cmd : xs) m

compileTopTerm :: TopTerm Desugared -> Compile [S.Def S.Exp]
compileTopTerm (DataTerm x _) = compileDatatype x
compileTopTerm (DefTerm x@(MkDef ident _ _ _) _) =
  if isBuiltin ident
  then return []
  else (:[]) <$> compileMultiHandlerDefinition x
compileTopTerm _ = return [] -- interfaces are ignored for now. add to a map?

-- a constructor is then just a cons cell of its arguments
-- how to do pattern matching correctly? maybe they are just n-adic functions
-- too? pure ones are just pure functions, etc.
compileDatatype :: DataT Desugared -> Compile [S.Def S.Exp]
compileDatatype (DT _ _ xs _) = mapM compileCtr xs

-- nonNullary :: [Ctr a] -> Compile [Ctr a]
-- nonNullary ((MkCtr id []) : xs) = do addAtom id
--                                      nonNullary xs
-- nonNullary (x : xs) = do xs' <- nonNullary xs
--                          return $ x : xs'
-- nonNullary [] = return []

compileCtr :: Ctr Desugared -> Compile (S.Def S.Exp)
compileCtr (Ctr ident [] _) = return $ S.DF ident [] [([], S.EA ident S.:& S.EA "")]
compileCtr (Ctr ident ts _) =
  let f x n = x ++ show n in
  let xs = replicate (length ts) "x" in
  let xs' = zipWith f xs [1..] in
  let args = map (S.PV . S.VPV) xs' in
  let e = foldr1 (S.:&) $ S.EA ident : (map S.EV xs' ++ [S.EA ""]) in
  return $ S.DF ident [] [(args, e)]

-- use the type to generate the signature of commands handled
-- generate a clause 1-to-1 correspondence
compileMultiHandlerDefinition :: MultiHandlerDefinition Desugared -> Compile (S.Def S.Exp)
compileMultiHandlerDefinition (MkDef id ty xs _) =
  do xs' <- mapM compileClause xs
     tyRep <- compileCompType ty
     return $ S.DF id tyRep xs'

compileCompType :: CompType Desugared -> Compile [([S.Adap], [String])]
compileCompType (CompType xs _ _) = mapM compilePort xs

compilePort :: Port Desugared -> Compile ([S.Adap], [String])
compilePort p@(Port adjs _ _) =
  do let (insts, adps) = adjsNormalForm adjs
     -- convert insts into list of commands
     let insts' = M.mapWithKey (\i insts ->
                                replicate ((length . bwd2fwd) insts) i) insts
     cmds <- concat <$> mapM getCCmds (concat (M.elems insts'))
     -- convert renamings into list of Adap
     let (ids, rens) = unzip (M.assocs adps)   -- (id, ren)
     rencmds <- mapM getCCmds ids
     return (zip rencmds rens, cmds)

compileClause :: Clause Desugared -> Compile ([S.Pat], S.Exp)
compileClause (MkClause ps tm _) = do
  ps' <- mapM compilePattern ps
  e <- compileTerm tm
  return (ps', e)

compilePattern :: Pattern Desugared -> Compile S.Pat
compilePattern (VPat x _) = S.PV <$> compileVPat x
compilePattern c@(CmdPat cmd n xs k _) = do xs' <- mapM compileVPat xs
                                            return $ S.PC cmd n xs' k
compilePattern (ThkPat id _) = return $ S.PT id

-- The current version simply represents Frank characters as one
-- character Shonky strings and Frank strings as a Shonky datatype
-- with "cons" and "nil" constructors.

compileVPat :: ValuePat Desugared -> Compile S.VPat
compileVPat (VarPat ident _) = return $ S.VPV ident
compileVPat (DataPat ident xs _) =
  case xs of
    []  -> return $ S.VPA ident S.:&: S.VPA ""
    xs -> do xs' <- mapM compileVPat xs
             return $ foldr1 (S.:&:) $ S.VPA ident : (xs' ++ [S.VPA ""])
compileVPat (IntPat n _) = return $ S.VPI n
compileVPat ((StrPat s a) :: ValuePat Desugared) = compileVPat (compileStrPat s) where
  compileStrPat :: String -> ValuePat Desugared
  compileStrPat []     = DataPat "nil" [] a
  compileStrPat (c:cs) = DataPat "cons" [CharPat c a, compileStrPat cs] a
compileVPat (CharPat c _) = return $ S.VPX [Left c]

compileTerm :: Term Desugared -> Compile S.Exp
compileTerm (SC sc _) = compileSComp sc
-- compileTerm MkLet = return $ S.EV "let"
compileTerm (StrTerm s a) = compileDataCon (f s) where
  f :: String -> DataCon Desugared
  f [] = DataCon "nil" [] a
  f (c:cs) = DataCon "cons" [CharTerm c a, DCon (f cs) a] a
compileTerm (IntTerm n _) = return $ S.EI n
compileTerm (CharTerm c _) = return $ S.EX [Left c]
compileTerm (TermSeq t1 t2 _) = (S.:!) <$> compileTerm t1 <*> compileTerm t2
compileTerm (Use u _) = compileUse u
compileTerm (DCon d _) = compileDataCon d

compileUse :: Use Desugared -> Compile S.Exp
compileUse (Op op _) = compileOp op
compileUse (App use xs _) = (S.:$) <$> compileUse use <*> mapM compileTerm xs
compileUse (Adapted [] t _) = compileUse t
compileUse (Adapted (r:rr) t a) =
  do (cs, r') <- compileAdaptor r
     rest <- compileUse (Adapted rr t a)
     return $ S.ER (cs, r') rest

compileAdaptor :: Adaptor Desugared -> Compile ([String], Renaming)
compileAdaptor adp@(CompilableAdp x m ns _) = do
  cmds <- getCCmds x
  return (cmds, adpToRen adp)


compileDataCon :: DataCon Desugared -> Compile S.Exp
compileDataCon (DataCon id xs _) = do xs' <- mapM compileTerm xs
                                      return (S.EV id S.:$ xs')

compileSComp :: SComp Desugared -> Compile S.Exp
compileSComp (SComp xs _) = S.EF <$> pure [([], [])] <*> mapM compileClause xs
-- TODO: LC: Fix this!

compileOp :: Operator Desugared -> Compile S.Exp
compileOp (Mono ident _) = case M.lookup ident builtins of
  Just v -> return $ S.EV v
  Nothing ->  do b <- isAtom ident
                 return $ if b then S.EA ident
                          else S.EV ident
compileOp (Poly ident _) = case M.lookup ident builtins of
  Just v -> return $ S.EV v
  Nothing -> return $ S.EV ident
compileOp (CmdIdentifier ident _) = return $ S.EA ident

builtins :: M.Map String String
builtins = M.fromList [("+", "plus")
                      ,("-", "minus")
                      ,("eqc" , "eqc")
                      ,(">", "gt")
                      ,("<", "lt")]

isBuiltin :: String -> Bool
isBuiltin x = M.member x builtins
