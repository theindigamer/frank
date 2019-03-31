{-# LANGUAGE LambdaCase #-}

module RefineSyntax where

import Control.Monad
import Control.Monad.Except
import Control.Monad.State
import Data.Foldable
import Data.Functor.Identity

import Data.List
import Data.Maybe
import qualified Data.Map.Strict as M
import qualified Data.Set as S

import BwdFwd
import Syntax
import RefineSyntaxCommon
import RefineSyntaxConcretiseEps
import RefineSyntaxSubstitItfAliases
import Debug

-- Main refinement function
refine :: Prog Raw -> Either String (Prog Refined)
refine prog = evalState (runExceptT (refine' prog)) initRefine

-- Explicit refinements:
-- + concretise epsilons in top level definitions
-- + built-in data types, interfaces, operators are added
refine' :: Prog Raw -> Refine (Prog Refined)
refine' (MkProg xs) = do
  -- Make sure datatypes have unique ids
  checkUniqueIds [d | (DataTerm d _) <- xs] (errorRefDuplTopTerm "datatype")
  -- Make sure interfaces and interface aliases have unique ids
  checkUniqueIds ([i | i@(ItfTerm _ _) <- xs] ++
                  [i | i@(ItfAliasTerm _ _) <- xs])
    (errorRefDuplTopTerm "interface/interface alias")
  -- Concretise epsilon vars
  let (dts, itfs, itfAls) = concretiseEps [d | DataTerm d _ <- xs]
                                          [i | ItfTerm i _ <- xs]
                                          [i | ItfAliasTerm i _ <- xs]
  let hdrSigs = [s | SigTerm s _ <- xs]
  let hdrDefs = [c | ClsTerm c _ <- xs]
  -- Initialise refinement state
  initialiseRState dts itfs itfAls hdrSigs
  -- Refine top level terms
  putTopLevelCtxt Datatype
  dtTerms <- mapM refineDataT dts
  putTopLevelCtxt Interface
  itfTerms <- mapM refineItf itfs
  putTopLevelCtxt InterfaceAlias
  itfAlTerms <- mapM refineItfAl itfAls
  putTopLevelCtxt Handler
  hdrs <- mapM (refineMH hdrDefs) hdrSigs
  -- Check uniqueness of hdrs w.r.t builtin ones
  -- checkUniqueIds ([h | (DefTerm h _) <- hdrs] ++ builtinMultiHandlerDefinitions)
  --   (errorRefDuplTopTerm "operator")
  return $ MkProg (map (\dt -> DataTerm dt a) builtinDataTs ++ dtTerms ++
                   map (\itf -> ItfTerm itf a) builtinItfs ++ itfTerms ++
                   map (\hdr -> DefTerm hdr a) builtinMultiHandlerDefinitions ++ hdrs)
  where a = Refined BuiltIn
{-# ANN refine' "HLint: ignore Avoid lambda" #-}

-- Explicit refinements:
-- + data type has unique effect & type variables
refineDataT :: DataT Raw -> Refine (TopTerm Refined)
refineDataT d@(DT dt ps ctrs a) =
 --         data dt p_1 ... p_m = ctr_1 | ... | ctr_n
  if uniqueIds (map fst ps) then
    do let tvs = [x | (x, VT) <- ps] -- val ty vars
       let evs = [x | (x, ET) <- ps] -- eff ty vars
       -- refine constructors
       putTMap (M.fromList $ zip tvs (map (swap TVar a) tvs)) -- temp. val ty vars
       putEVSet (S.fromList evs)                       -- temp. eff ty vars
       ctrs' <- mapM refineCtr ctrs
       putEVSet S.empty                                -- reset
       putTMap M.empty                                 -- reset
       return $ DataTerm (DT dt ps ctrs' a') a'
  else throwError $ errorRefDuplParamData d
  where a' = rawToRef a

-- Explicit refinements:
-- + interface has unique effect & type variables
refineItf :: Itf Raw -> Refine (TopTerm Refined)
refineItf i@(Itf itf ps cmds a) =
--        interface itf p_1 ... p_m = cmd_1 | ... | cmd_n
  if uniqueIds (map fst ps) then
    do let tvs = [x | (x, VT) <- ps] -- val ty vars
       let evs = [x | (x, ET) <- ps] -- eff ty vars
       -- refine commands
       putTMap (M.fromList $ zip tvs (map (swap TVar a) tvs)) -- temp. val ty vars
       putEVSet (S.fromList evs)                       -- temp. eff ty vars
       cmds' <- mapM refineCmd cmds
       putEVSet S.empty                                -- reset
       putTMap M.empty                                 -- reset
       return $ ItfTerm (Itf itf ps cmds' a') a'
  else throwError $ errorRefDuplParamItf i
  where a' = rawToRef a

-- Explicit refinements:
-- + interface has unique effect & type variables
refineItfAl :: ItfAlias Raw -> Refine (ItfAlias Refined)
refineItfAl i@(ItfAlias itfAl ps _ a) =
--          interface itf p_1 ... p_m = [itf_1 t_11 ... t_1n, ...]
  if uniqueIds (map fst ps) then
    do let tvs = [x | (x, VT) <- ps] -- val ty vars
       let evs = [x | (x, ET) <- ps] -- eff ty vars
       -- refine itf map
       putTMap (M.fromList $ zip tvs (map (swap TVar a) tvs)) -- temp. val ty vars
       putEVSet (S.fromList evs)                       -- temp. eff ty vars
       -- interpret RHS of interface alias def. as the instantiation of itf with
       -- the generic type variables ps (this "lift" is possible as the
       -- itf map of itf is part of the RState)
       let singletonItfMap = ItfMap (M.singleton itfAl (BEmp :< map tyVar2rawTyVarArg ps)) (Raw Generated)
       itfMap' <- refineItfMap singletonItfMap
       putEVSet S.empty                                -- reset
       putTMap M.empty                                 -- reset
       return $ ItfAlias itfAl ps itfMap' a'
  else throwError $ errorRefDuplParamItfAl i
  where a' = rawToRef a

-- Explicit refinements:
-- + command has unique effect & type variables
refineCmd :: Cmd Raw -> Refine (Cmd Refined)
refineCmd c@(Cmd id ps xs y a) =
--        id p_1 ... p_m: x_1 -> ... -> x_n -> y
  if uniqueIds (map fst ps) then
    do tmap <- getTMap
       evset <- getEVSet
       -- TODO: LC: Shadowing should be allowed, fix this in future
       -- check that none of this cmd's ty vars coincide with the itf's ones
       if uniqueIds (map fst ps ++ map fst (M.toList tmap) ++ S.toList evset) then
         do let tvs = [x | (x, VT) <- ps] -- val ty vars
            let evs = [x | (x, ET) <- ps] -- eff ty vars
            -- refine ty args
            putTMap (M.union tmap (M.fromList $ zip tvs (map (swap TVar a) tvs))) -- temp. val ty vars
            putEVSet (S.union evset (S.fromList evs))    -- temp. eff ty vars
            xs' <- mapM refineVType xs
            y' <- refineVType y
            putTMap tmap                                 -- reset
            putEVSet evset                               -- reset
            return $ Cmd id ps xs' y' a'
       else throwError $ "a type parameter of command " ++ id ++
                         "already occurs as interface type parameter"
  else throwError $ errorRefDuplParamCmd c
  where a' = rawToRef a


refineCtr :: Ctr Raw -> Refine (Ctr Refined)
refineCtr (Ctr id xs a) = do xs' <- mapM refineVType xs
                             return $ Ctr id xs' (rawToRef a)

refineCType :: CType Raw -> Refine (CType Refined)
refineCType (CType xs z a) = do ys <- mapM refinePort xs
                                peg <- refinePeg z
                                return $ CType ys peg (rawToRef a)

refinePort :: Port Raw -> Refine (Port Refined)
refinePort (Port adjs ty a) = do adjs' <- mapM refineAdj adjs
                                 ty' <- refineVType ty
                                 return $ Port (concat adjs') ty' (rawToRef a)

refinePeg :: Peg Raw -> Refine (Peg Refined)
refinePeg (Peg ab ty a) = do ab' <- refineAb ab
                             ty' <- refineVType ty
                             return $ Peg ab' ty' (rawToRef a)

refineAb :: Ab Raw -> Refine (Ab Refined)
refineAb ab@(Ab v mp@(ItfMap m _) a) =
--       [v | itf_1 x_11 ... x_1k, ..., itf_l x_l1 ... x_ln]
  do -- Check that v has been introduced before or is now implicitly introduced
     evset <- getEVSet
     ctx <- getTopLevelCtxt
     case v of
       (EmpAb b) -> do m' <- refineItfMap mp
                       return $ Ab (EmpAb (rawToRef b)) m' a'
       (AbVar x b) ->
         if x `S.member` evset || isHeaderContext ctx then
            do m' <- refineItfMap mp
               return $ Ab (AbVar x (rawToRef b)) m' a'
         else throwError $ errorRefIdNotDeclared "effect type variable" x a
  where a' = rawToRef a

-- Input: itf_1 x_11 ... x_1k, ..., itf_l x_l1 ... x_ln
-- If a itf_i is an already-introduced effect variable, require that there are
--   no x_ij (else throw error)
-- Output: all itf_i which refer to already-introduced effect variables
getIntroducedEVars :: ItfMap Raw -> Refine [Identifier]
getIntroducedEVars (ItfMap m _) = do
  p <- getEVSet
  let candidates = [(itf, (maximum . map length . bwd2fwd) xs) | (itf, xs) <- M.toList m, S.member itf p]
  let errors = filter (\(itf, n) -> n > 0) candidates
  case errors of []             -> return $ map fst candidates
                 ((itf, _) : _) -> throwError $ errorRefEffVarNoParams itf

refineAbMod :: AbMod Raw -> AbMod Refined
refineAbMod (EmpAb a) = EmpAb (rawToRef a)
refineAbMod (AbVar x a) = AbVar x (rawToRef a)

refineAdj :: Adjustment Raw -> Refine [Adjustment Refined]
refineAdj (ConsAdj x ts a) = do
  tss' <- refineItfInst a (x, ts)
  let tss'' = M.foldlWithKey (\acc itf ts' -> acc ++ instsToAdjs itf ts') [] tss'
  --LAST STOP
  pure tss''
  where instsToAdjs :: Identifier -> Bwd [TyArg Refined] -> [Adjustment Refined]
        instsToAdjs itf ts = map (\ts' -> ConsAdj itf ts' (rawToRef a)) (bwd2fwd ts)
refineAdj (AdaptorAdj adp a) = do
  adp' <- refineAdaptor adp
  pure [AdaptorAdj adp' (rawToRef a)]

-- Explicit refinements:
-- + interface aliases are substituted
refineItfInst :: Raw -> (Identifier, [TyArg Raw]) ->
                 Refine (M.Map Identifier (Bwd [TyArg Refined]))
refineItfInst a (x, ts) = do
  --                  x t_11 ... t_1n
  -- replace interface aliases by interfaces
  m' <- substitItfAls (x, ts) >>= \case
    ItfMap m _ -> pure m
    _ -> throwError "Expected ItfMap but found something else."
  --                  x t_11 ... t_1n, ..., x t_m1 t_mn
  -- refine instantiations of each interface
  M.fromList <$> mapM (refineItfInsts a) (M.toList m')

-- Explicit refinements:
-- + interface aliases are substituted
refineItfMap :: ItfMap Raw -> Refine (ItfMap Refined)
refineItfMap (ItfMap m a) = do
  -- replace interface aliases by interfaces
  ms <- mapM (\(x, insts) -> mapM (\inst -> substitItfAls (x, inst)) (bwd2fwd insts)) (M.toList m)
  let (ItfMap m' a') = foldl plusItfMap (emptyItfMap a) (concat ms)
  -- refine instantiations of each interface
  m'' <- M.fromList <$> mapM (refineItfInsts a) (M.toList m')
  return $ ItfMap m'' (rawToRef a)

refineItfInsts :: Raw -> (Identifier, Bwd [TyArg Raw]) ->
                  Refine (Identifier, Bwd [TyArg Refined])
refineItfInsts a (x, insts) = do
--                  x t_11 ... t_1n, ..., x t_m1 t_mn
  itfs <- getRItfs
  case M.lookup x itfs of
    Just ps -> do
--            1) interface x p_1 ... p_n     = ...
--         or 2) interface x p_1 ... p_n [£] = ...
--               and [£] has been explicitly added before
--            if 2), set t_{n+1} := [£]
       evset <- getEVSet
       ctx <- getTopLevelCtxt
       insts' <- mapM (\ts -> do let a' = Raw (implicitNear a)
                                 let ts' = if "£" `S.member` evset ||
                                              isHeaderContext ctx
                                           then concretiseEpsArg ps ts a'
                                           else ts
                                 checkArgs x (length ps) (length ts') a
                                 mapM refineTyArg ts')
                      insts
       return (x, insts')
    Nothing -> throwError $ errorRefIdNotDeclared "interface" x a

-- Explicit refinements:
-- + implicit [£] ty args to data types are made explicit
-- + DTTy is distinguished between being (in the following precedence)
--   1) data type indeed            -> DTTy
--   2) (implicitly) intro'd ty var -> TVar  (if no ty args)
--   3) neither                     -> error
-- + MkTVar is distinguished between being
--   1) intro'd ty var              -> TVar
--   2) data type                   -> DTTy
--   3) neither                     -> TVar
-- + ty arguments refer only to introduced val tys
refineVType :: VType Raw -> Refine (VType Refined)
refineVType (DTTy x ts a) =
--           x t_1 ... t_n
  do -- Check that x is datatype or introduced or just-implicitly intro'd ty var
     dtm <- getRDTs
     tmap <- getTMap
     ctx <- getTopLevelCtxt
     evset <- getEVSet
     case M.lookup x dtm of
       Just ps -> do
--       data x p_1 ... p_n
         let a' = Raw (implicitNear a)
         let ts' = if "£" `S.member` evset || isHeaderContext ctx
                   then concretiseEpsArg ps ts a'
                   else ts
         checkArgs x (length ps) (length ts') a
         ts'' <- mapM refineTyArg ts'
         return $ DTTy x ts'' (rawToRef a)
       Nothing ->
         if null ts &&          -- there must be no arguments to ty var
            (isHeaderContext ctx ||   -- x can be implic. ty var in hdr sign.
             x `M.member` tmap)    -- x can be in val ty contexts
         then return $ TVar x (rawToRef a)
         else throwError $ errorRefIdNotDeclared "value type variable" x a
refineVType (SCTy ty a) = swap SCTy (rawToRef a) <$> refineCType ty
refineVType (TVar x a) =
  do -- Check that x is intro'd ty-var or datatype or just-implicitly intro'd ty var
     tmap <- getTMap
     dtm <- getRDTs
     ctx <- getTopLevelCtxt
     case M.lookup x tmap of
       Just _  -> return $ TVar x (rawToRef a)
       Nothing -> case M.lookup x dtm of
         Just ps ->
           -- if the data type is parameterised by a single eff var then instantiate it to [£|]
           do let ts = case ps of
                         [(_, ET)] -> [EArg (Ab (AbVar "£" a) (ItfMap M.empty a) a) a]
                         _ -> []
              checkArgs x (length ps) (length ts) a
              ts' <- mapM refineTyArg ts
              return $ DTTy x ts' (rawToRef a)
         Nothing ->
           -- last possibility: x can be implic. ty var in hdr sign.
           if isHeaderContext ctx
           then return $ TVar x (rawToRef a)
           else throwError $ errorRefIdNotDeclared "value type variable" x a
refineVType (StringTy a) = return $ StringTy (rawToRef a)
refineVType (IntTy a) = return $ IntTy (rawToRef a)
refineVType (CharTy a) = return $ CharTy (rawToRef a)

refineTyArg :: TyArg Raw -> Refine (TyArg Refined)
refineTyArg (VArg t a) = VArg <$> refineVType t <*> pure (rawToRef a)
refineTyArg (EArg ab a) = EArg <$> refineAb ab <*> pure (rawToRef a)

refineMH :: [MHCls Raw] -> MultiHandlerSignature Raw -> Refine (TopTerm Refined)
refineMH xs (Sig id ty a) = do cs <- mapM refineMHCls ys
                               ty' <- refineCType ty
                               return $ DefTerm (Def id ty' cs a') a'
  where ys = filter (\(MHCls id' _ _) -> id' == id) xs
        a' = rawToRef a

refineMHCls :: MHCls Raw -> Refine (Clause Refined)
refineMHCls (MHCls _ cls a) = refineClause cls

-- Explicit refinements:
-- + id "x" is refined to 1) DataCon:          0-ary constructor if matching
--                        2) Use . Op . CmdIdentifier: command operator if matching
--                        3) Use . Op . Poly:  poly multihandler operator if it exists
--                        4) Use . Op . Mono:  mono multihandler
-- + applications (MkRawComb) are refined same way as ids
-- + let x = e1 in e2    -->   case e1 {x -> e2}
-- + [x, y, z]           -->   x cons (y cons (z cons nil))
refineUse :: Use Raw -> Refine (Either (Use Refined) (Term Refined))
refineUse (RawIdentifier id a) =
  do ctrs <- getRCtrs
     cmds <- getRCmds
     hdrs <- getRMHs
     case id `findPair` ctrs of
        Just n -> do checkArgs id n 0 a
                     return $ Right $ DCon (DataCon id [] a') a'
        Nothing ->
          case id `findPair` cmds of
            Just n -> return $ Left $ Op (CmdIdentifier id a') a'
            -- TODO: LC: Do we need to check command's arity = 0?
            Nothing ->
              case id `findPair` hdrs of
                -- polytypic (n=0 means: takes no argument, x!)
                Just n -> return $ Left $ Op (Poly id a') a'
                -- TODO: LC: Same here, check for handler's arity = 0?
                -- monotypic: must be local variable
                Nothing -> return $ Left $ Op (Mono id a') a'
  where a' = rawToRef a
refineUse (RawComb (RawIdentifier id b) xs a) =
  do xs' <- mapM refineTerm xs
     ctrs <- getRCtrs
     cmds <- getRCmds
     hdrs <- getRMHs
     case id `findPair` ctrs of
        Just n -> do checkArgs id n (length xs') a
                     return $ Right $ DCon (DataCon id xs' b') a'
        Nothing ->
          case id `findPair` cmds of
            Just n -> do checkArgs id n (length xs') a
                         return $ Left $ App (Op (CmdIdentifier id b') b') xs' a'
            Nothing ->
              case id `findPair` hdrs of
                Just n -> do checkArgs id n (length xs') a
                             return $ Left $ App (Op (Poly id b') b') xs' a'
                Nothing -> return $ Left $ App (Op (Mono id b') b') xs' a'
  where a' = rawToRef a
        b' = rawToRef b
refineUse (RawComb x xs a) =
  do x' <- refineUse x
     case x' of
       Left use -> do xs' <- mapM refineTerm xs
                      return $ Left $ App use xs' (rawToRef a)
       Right tm -> throwError $ errorRefExpectedUse tm
refineUse (Adapted rs t a) =
  -- First check the existence of the interfaces
  do rs' <- mapM refineAdaptor rs
     t' <- refineUse t
     case t' of
       Left u   -> return $ Left $ Adapted rs' u (rawToRef a)
       Right tm -> throwError $ errorRefExpectedUse tm

refineAdaptor :: Adaptor Raw -> Refine (Adaptor Refined)
refineAdaptor adp@(RawAdp x liat left right a) = do
  itfCx <- getRItfs
  if x `M.member` itfCx then
    -- TODO: LC: left-hand side must consist of distinct names
    -- Check whether first element of right-hand side is liat
    if null right || head right == liat then
      if null right then return $ Adp x Nothing [] (rawToRef a)
      else
        let mm = Just (length left) in
        let right' = tail right in
        let rightNs = map (\p -> elemIndex p (reverse left)) right' in
        if any isNothing rightNs then throwError "adaptor error"
        else return $ Adp x (Just (length left)) (map fromJust rightNs) (rawToRef a)
    else
      throwError "adaptor error"
  else throwError $ errorRefIdNotDeclared "interface" x a

refineTerm :: Term Raw -> Refine (Term Refined)
refineTerm (Let x t1 t2 a) =
  do s1 <- refineTerm t1
     s2 <- refineTerm $ SC (SComp [Cls [VPat (VarPat x a) a] t2 a] a) a
     return $ Use (App (Op (Poly "case" a') a') [s1, s2] a') a'
  where a' = rawToRef a
refineTerm (SC x a) = do x' <- refineSComp x
                         return $ SC x' (rawToRef a)
refineTerm (StrTerm x a) = return $ StrTerm x (rawToRef a)
refineTerm (IntTerm x a) = return $ IntTerm x (rawToRef a)
refineTerm (CharTerm x a) = return $ CharTerm x (rawToRef a)
refineTerm (ListTerm ts a) =
  do ts' <- mapM refineTerm ts
     return $
       foldr
         (\x y -> DCon (DataCon "cons" [x, y] a') a')
         (DCon (DataCon "nil" [] a') a')
         ts'
  where a' = rawToRef a
refineTerm (TermSeq t1 t2 a) = do t1' <- refineTerm t1
                                  t2' <- refineTerm t2
                                  return $ TermSeq t1' t2' (rawToRef a)
refineTerm (Use u a) = do u' <- refineUse u
                          case u' of
                            Left use -> return $ Use use (rawToRef a)
                            Right tm -> return tm

refineSComp :: SComp Raw -> Refine (SComp Refined)
refineSComp (SComp xs a) = do xs' <- mapM refineClause xs
                              return $ SComp xs' (rawToRef a)

refineClause :: Clause Raw -> Refine (Clause Refined)
refineClause (Cls ps tm a) = do ps' <- mapM refinePattern ps
                                tm' <- refineTerm tm
                                return $ Cls ps' tm' (rawToRef a)

-- Explicit refinements:
-- + command patterns (e.g. <send x -> k>) must refer to existing command and
--   match # of args
refinePattern :: Pattern Raw -> Refine (Pattern Refined)
refinePattern (VPat p a) = VPat <$> refineVPat p <*> pure (rawToRef a)
refinePattern (CmdPat x n ps k a) =
  do cmds <- getRCmds
     case x `findPair` cmds of
       Just n' -> do checkArgs x n' (length ps) a
                     ps' <- mapM refineVPat ps
                     return $ CmdPat x n ps' k (rawToRef a)
       Nothing -> throwError $ errorRefIdNotDeclared "command" x a
refinePattern (ThkPat x a) = return $ ThkPat x (rawToRef a)

-- Explicit refinements:
-- + variable patterns, e.g. "x", are refined to ctrs if "x" is 0-ary ctr
-- + data patterns have to be fully instantiated constructors
-- + cons (%::%) and list patterns ([%, %, %]) become data patterns (cons exps)
refineVPat :: ValuePat Raw -> Refine (ValuePat Refined)
refineVPat (VarPat x a) =
  do ctrs <- getRCtrs
     case x `findPair` ctrs of
       Just n -> do checkArgs x n 0 a
                    return $ DataPat x [] (rawToRef a)
       Nothing -> return $ VarPat x (rawToRef a)
refineVPat (DataPat x xs a) =
  do ctrs <- getRCtrs
     case x `findPair` ctrs of
       Just n -> do checkArgs x n (length xs) a
                    xs' <- mapM refineVPat xs
                    return $ DataPat x xs' (rawToRef a)
       Nothing -> throwError $ errorRefIdNotDeclared "constructor" x a
refineVPat (IntPat i a) = return $ IntPat i (rawToRef a)
refineVPat (CharPat c a) = return $ CharPat c (rawToRef a)
refineVPat (StrPat s a) = return $ StrPat s (rawToRef a)
refineVPat (ConsPat x xs a) =
  do x' <- refineVPat x
     xs' <- refineVPat xs
     return $ DataPat "cons" [x', xs'] (rawToRef a)
refineVPat (ListPat ps a) =
  do ps' <- mapM refineVPat ps
     return $
       foldr
         (\x y -> DataPat "cons" [x, y] (rawToRef a))
         (DataPat "nil" [] (rawToRef a))
         ps'

initialiseRState :: [DataT Raw] -> [Itf Raw] -> [ItfAlias Raw] -> [MultiHandlerSignature Raw] -> Refine ()
initialiseRState dts itfs itfAls hdrs =
  do i <- getRState
     itfs'   <- foldM addItf      (interfaces i)       itfs
     itfAls' <- foldM addItfAlias (interfaceAliases i) itfAls
     dts'    <- foldM addDataT    (datatypes i)        dts
     hdrs'   <- foldM addMH       (handlers i)         hdrs
     cmds'   <- foldM addCmd      (cmds i)             (concatMap getCmds itfs)
     ctrs'   <- foldM addCtr      (ctrs i)             (concatMap getCtrs dts)
     putRItfs       itfs'
     putRItfAliases itfAls'
     putRDTs        dts'
     putRCmds       cmds'
     putRCtrs       ctrs'
     putRMHs        hdrs'

makeIntBinOp :: Refined -> Char -> MultiHandlerDefinition Refined
makeIntBinOp a c = Def [c] (CType [Port [] (IntTy a) a
                                  ,Port [] (IntTy a) a]
                                  (Peg (Ab (AbVar "£" a) (ItfMap M.empty a) a) (IntTy a) a) a) [] a

makeIntBinCmp :: Refined -> Char -> MultiHandlerDefinition Refined
makeIntBinCmp a c = Def [c] (CType [Port [] (IntTy a) a
                                   ,Port [] (IntTy a) a]
                             (Peg (Ab (AbVar "£" a) (ItfMap M.empty a) a)
                              (DTTy "Bool" [] a) a) a) [] a

{-- The initial state for the refinement pass. -}

builtinDataTs :: [DataT Refined]
builtinDataTs = [DT "List" [("X", VT)] [Ctr "cons" [TVar "X" b
                                                       ,DTTy "List" [VArg (TVar "X" b) b] b] b
                                         ,Ctr "nil" [] b] b
                ,DT "Unit" [] [Ctr "unit" [] b] b
                ,DT "Bool" [] [Ctr "true" [] b, Ctr "false" [] b] b
                ,DT "Ref" [("X", VT)] [] b]
  where b = Refined BuiltIn

builtinItfs :: [Itf Refined]
builtinItfs = [Itf "Console" [] [Cmd "inch" [] [] (CharTy b) b
                                ,Cmd "ouch" [] [CharTy b]
                                 (DTTy "Unit" [] b) b
                                ,Cmd "ouint" [] [IntTy b]
                                 (DTTy "Unit" [] b) b] b
              ,Itf "RefState" [] [Cmd "new" [("X", VT)] [TVar "X" b]
                                                            (DTTy "Ref" [VArg (TVar "X" b) b] b) b
                                   ,Cmd "write" [("X", VT)] [DTTy "Ref" [VArg (TVar "X" b) b] b
                                                             ,TVar "X" b]
                                                             (DTTy "Unit" [] b) b
                                   ,Cmd "read" [("X", VT)] [DTTy "Ref" [VArg (TVar "X" b) b] b]
                                                              (TVar "X" b) b] b]
  where b = Refined BuiltIn

builtinItfAliases :: [ItfAlias Raw]
builtinItfAliases = []

builtinMultiHandlerDefinitions :: [MultiHandlerDefinition Refined]
builtinMultiHandlerDefinitions = map (makeIntBinOp (Refined BuiltIn)) "+-" ++
                map (makeIntBinCmp (Refined BuiltIn)) "><" ++
                [caseDef, charEq, alphaNumPred]

charEq :: MultiHandlerDefinition Refined
charEq = Def "eqc" (CType [Port [] (CharTy a) a
                          ,Port [] (CharTy a) a]
                          (Peg (Ab (AbVar "£" a) (ItfMap M.empty a) a)
                               (DTTy "Bool" [] a) a) a) [] a
  where a = Refined BuiltIn

alphaNumPred :: MultiHandlerDefinition Refined
alphaNumPred = Def "isAlphaNum"
               (CType [Port [] (CharTy a) a]
                          (Peg (Ab (AbVar "£" a) (ItfMap M.empty a) a)
                               (DTTy "Bool" [] a) a) a) [] a
  where a = Refined BuiltIn

caseDef :: MultiHandlerDefinition Refined
caseDef = Def
          "case"
          (CType
            [Port [] (TVar "X" b) b
            ,Port []
             (SCTy (CType [Port [] (TVar "X" b) b]
                      (Peg (Ab (AbVar "£" b) (ItfMap M.empty b) b) (TVar "Y" b) b) b) b) b]
            (Peg (Ab (AbVar "£" b) (ItfMap M.empty b) b) (TVar "Y" b) b) b)
          [Cls
            [VPat (VarPat "x" b) b, VPat (VarPat "f" b) b]
            (Use (App (Op (Mono "f" b) b) [Use (Op (Mono "x" b) b) b] b) b) b] b
  where b = Refined BuiltIn

builtinMHs :: [IPair]
builtinMHs = map add builtinMultiHandlerDefinitions
  where add (Def x (CType ps _ a) _ _) = (x,length ps)

builtinDTs :: DataTypeMap
builtinDTs = foldl add M.empty builtinDataTs
  where add m (DT id ps _ a) = M.insert id ps m

builtinIFs :: IFMap
builtinIFs = foldl add M.empty builtinItfs
  where add m (Itf id ps _ a) = M.insert id ps m

builtinIFAliases :: IFAliasesMap
builtinIFAliases = foldl add M.empty builtinItfAliases
  where add m (ItfAlias id ps itfMap a) = M.insert id (ps, itfMap) m

builtinCtrs :: [IPair]
builtinCtrs = map add $ concatMap getCtrs builtinDataTs
  where add (Ctr id ts a) = (id,length ts)

builtinCmds :: [IPair]
builtinCmds = map add $ concatMap getCmds builtinItfs
  where add (Cmd id _ ts _ a) = (id,length ts)

initRefine :: RState
initRefine = MkRState builtinIFs builtinIFAliases builtinDTs builtinMHs builtinCtrs
             builtinCmds M.empty S.empty Nothing

{- Helper functions -}

mem :: Identifier -> [IPair] -> Bool
mem x xs = x `elem` map fst xs

findPair :: Identifier -> [IPair] -> Maybe Int
findPair x ((y,n) : xs) = if x == y then Just n else findPair x xs
findPair _ _ = Nothing

collectCmds :: [Cmd a] -> [Identifier]
collectCmds (Cmd cmd _ _ _ a : xs) = cmd : collectCmds xs
collectCmds [] = []

collectCtrs :: [Ctr a] -> [Identifier]
collectCtrs (Ctr ctr _ a : xs) = ctr : collectCtrs xs
collectCtrs [] = []

collectMHNames :: [MultiHandlerSignature Raw] -> [Identifier]
collectMHNames (Sig hdr _ a : xs) = hdr : collectMHNames xs
collectMHNames [] = []

-- Add the id if not already present
addEntry :: [IPair] -> Identifier -> Int -> String -> Refine [IPair]
addEntry xs x n prefix = if x `mem` xs then throwError (errorRefEntryAlreadyDefined prefix x)
                         else return $ (x,n) : xs

addItf :: IFMap -> Itf Raw -> Refine IFMap
addItf m (Itf x ps _ a) = return $ M.insert x ps m

addItfAlias :: IFAliasesMap -> ItfAlias Raw -> Refine IFAliasesMap
addItfAlias m (ItfAlias x ps itfMap a) = return $ M.insert x (ps, itfMap) m

addDataT :: DataTypeMap -> DataT Raw -> Refine DataTypeMap
addDataT m (DT x ps _ a) =
  if M.member x m then
    throwError $ errorRefDuplTopTerm "datatype" x (getSource a)
  else return $ M.insert x ps m

addCtr :: [IPair] -> Ctr a -> Refine [IPair]
addCtr xs (Ctr x ts a) = addEntry xs x (length ts) "duplicate constructor: "

addCmd :: [IPair] -> Cmd a -> Refine [IPair]
addCmd xs (Cmd x _ ts _ a) = addEntry xs x (length ts) "duplicate command: "

-- takes map handler-id -> #-of-ports and adds another handler entry
addMH :: [IPair] -> MultiHandlerSignature Raw -> Refine [IPair]
addMH xs (Sig x (CType ps p _) _) =
  addEntry xs x (length ps) "duplicate operator:"

uniqueIds :: [Identifier] -> Bool
uniqueIds xs = length xs == length (nub xs)

-- Helpers

checkArgs :: Identifier -> Int -> Int -> Raw -> Refine ()
checkArgs x exp act a =
  when (exp /= act) $
    throwError $ errorRefNumberOfArguments x exp act a

swap :: (a -> b -> c) -> b -> a -> c
swap f b a = f a b

rawToRef :: Raw -> Refined
rawToRef (Raw loc) = Refined loc
