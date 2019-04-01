-- Inspired by Adam Gundry et al.'s treatment of type inference in
-- context. See Gundry's thesis (most closely aligned) or the paper ``Type
-- inference in Context'' for more details.
{-# LANGUAGE GADTs #-}
module TypeCheck where

import Control.Monad
import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.State hiding (modify)

import Data.List.Unique

import qualified Data.Set as S
import qualified Data.Map.Strict as M

import BwdFwd
import Syntax
import FreshNames
import TypeCheckCommon
import Unification
import Debug

import Shonky.Renaming

type EVMap a = M.Map Identifier (Ab a)

-- Given an operator, reconstruct its corresponding type assigned via context
-- 1) x is command of interface itf:
--    - Retrieve how itf is instantiated in amb
--    - Add mark and add all type variables qs to context (-> qs')
--    - Unify itf instantiation ps with qs'
--    - Construct susp. comp. val. type whose containted tys are all in current locality
-- 2) x is monotypic (i.e., local variable) or
--         polytypic (i.e., multi-handler)
--    - It must have been assigned a type in the context, return it
find :: Operator Desugared -> Contextual (ValueType Desugared)
find (CmdIdentifier x a) =
  do amb <- getAmbient
     (itf, qs, rs, ts, y) <- getCmd x
     -- interface itf q_1 ... q_m = x r1 ... r_l: t_1 -> ... -> t_n -> y
     mps <- lkpInterface itf 0 amb -- Retrieve how itf is instantiated in amb
     addMark                 -- Localise qs
     -- Make mps flexible if it is not yet and store as res
     res <- case mps of
       Nothing ->
         do b <- isMVarDefined x
            if b then return mps
              else do ps <- mapM (makeFlexibleTypeArg []) qs
                      v <- freshMVar "E"
                      let m = InterfaceMap (M.fromList [(itf, BEmp :< ps)]) a
                      unifyAb amb (Ab (AbFVar v a) m a)
                      return $ Just ps
       Just _ -> return mps
     logBeginFindCmd x itf mps
     case res of
       Nothing -> throwError $ errorFindCmdNotPermit x a itf amb
       Just ps ->
         -- instantiation in ambient: [itf p_1 ... p_m]
         do -- bind qs to their instantiations (according to adjustment) and
            -- localise their occurences in ts, y
            qs' <- mapM (makeFlexibleTypeArg []) qs
            ts' <- mapM (makeFlexible []) ts
            y' <- makeFlexible [] y
            zipWithM_ unifyTypeArg ps qs'
            -- Localise rs
            rs' <- mapM (makeFlexibleTypeArg []) rs
            let ty = SCTy (CompType (map (\x -> Port [] x a) ts')
                                 (Peg amb y' a) a) a
            logEndFindCmd x ty
            return ty
find x = getContext >>= find'
  where find' BEmp = throwError $ errorTCNotInScope x
        find' (es :< TermVar y ty) | stripAnn x == stripAnn y = return ty
        find' (es :< _) = find' es

-- Find the first flexible type definition (as opposed to a hole) in ctx for x
findFTVar :: Identifier -> Contextual (Maybe (ValueType Desugared))
findFTVar x = getContext >>= find'
  where find' BEmp = return Nothing
        find' (es :< FlexMVar y (TyDefn ty)) | x == y = return $ Just ty
        find' (es :< _) = find' es

-- Run a contextual computation with an additonal term variable in scope
-- 1) Push [x:=ty] on context
-- 2) Run computation m
-- 3) Remove [x:=ty] from context
inScope :: Operator Desugared -> ValueType Desugared -> Contextual a -> Contextual a
inScope x ty m = do modify (:< TermVar x ty)
                    a <- m
                    modify dropVar
                    return a
  where dropVar :: Context -> Context
        dropVar BEmp = error "Invariant violation"
        dropVar (es :< TermVar y _) | stripAnn x == stripAnn y = es
        dropVar (es :< e) = dropVar es :< e

-- Run a contextual computation in a modified ambient environment
inAmbient :: Ab Desugared -> Contextual a -> Contextual a
inAmbient amb m = do oldAmb <- getAmbient
                     putAmbient amb
                     a <- m
                     putAmbient oldAmb
                     return a

-- Return the n-th right-most instantiation of the interface in the given
-- ability. Return Nothing if the interface is not part of the ability.
lkpInterface :: Identifier -> Int -> Ab Desugared -> Contextual (Maybe [TypeArg Desugared])
lkpInterface itf n (Ab v (InterfaceMap m _) _) =
  case M.lookup itf m of
    Just xs
      | length (bwd2fwd xs) > n -> return $ Just (bwd2fwd xs !! (length (bwd2fwd xs) - n - 1))
      | otherwise               -> lkpInterfaceInAbMod itf (n - length (bwd2fwd xs)) v
    _ -> lkpInterfaceInAbMod itf n v

lkpInterfaceInAbMod :: Identifier -> Int-> AbMod Desugared -> Contextual (Maybe [TypeArg Desugared])
lkpInterfaceInAbMod itf n (AbFVar x _) = getContext >>= find'
  where find' BEmp = return Nothing
        find' (es :< FlexMVar y (AbDefn ab)) | x == y = lkpInterface itf n ab
        find' (es :< _) = find' es
lkpInterfaceInAbMod itf n v = return Nothing

-- The only operators that could potentially be polymorphic are
-- 1) polytypic operators and
-- 2) command operators
-- We only instantiate here in case 1) because command operators get already
-- instantiated in "find"
-- LC: TODO: remove this function and transfer its functionality to "find", too?
instantiate :: Operator Desugared -> ValueType Desugared -> Contextual (ValueType Desugared)
instantiate (Poly _ _) ty = addMark >> makeFlexible [] ty
instantiate _ ty = return ty
-- TODO: change output of check to Maybe String?

-- infer the type of a use w.r.t. the given program
inferEvalUse :: Program Desugared -> Use Desugared ->
                Either String (Use Desugared, ValueType Desugared)
inferEvalUse p use = runExcept $ evalFreshMT $ evalStateT comp initTCState
  where comp = unCtx $ do _ <- initContextual p
                          inferUse use

-- Main typechecking function
-- + Init TCState
-- + Check each top term
-- + If no exception is thrown during checkTopTerm, return input program
check :: Program Desugared -> Either String (Program Desugared)
check p = runExcept $ evalFreshMT $ evalStateT (checkProgram p) initTCState
  where
    checkProgram p = unCtx $ do MkProgram xs <- initContextual p
                                theCtx <- getContext
                                xs' <- mapM checkTopTerm xs
                                return $ MkProgram xs'

checkTopTerm :: TopTerm Desugared -> Contextual (TopTerm Desugared)
checkTopTerm (DefTerm def a) = DefTerm <$> checkMultiHandlerDefinition def <*> pure a
checkTopTerm x = return x

checkMultiHandlerDefinition :: MultiHandlerDefinition Desugared -> Contextual (MultiHandlerDefinition Desugared)
checkMultiHandlerDefinition (MkDef id ty@(CompType ps q _) cs a) = do
  ty' <- validateCompType ty
  cs' <- mapM (checkCls ty') cs
  return $ MkDef id ty' cs' a

-- 1st major TC function besides "check": Infer type of a "use"
-- Functions below implement the typing rules described in the paper.
-- 1) Var, PolyVar, Command rules
--    - Find operator x in context and retrieve its type
--    - Case distinction on x:
--      1.1) x is monotypic (local var)
--           - Its type is exactly determined (instantiate does nothing)
--      1.2) x is polytypic (multi-handler) or a command
--           - Its type (susp. comp. ty) possibly contains rigid ty vars
--           - Instantiate all of them (add to context), then return type
-- 2) App rule
--    - Infer type of f
--    - If this susp. comp. type is known, check the arguments are well-typed
--    - If not, create fresh type pattern and unify (constraining for future)
-- 3) Lift rule
--    - Get ambient and expand it (substitute all flexible variables)
--    - Check that instances to be lifted are applicable for this ambient:
--      - Check "(amb - lifted) + lifted = amb"
--    - Recursively infer use of term, but under ambient "amb - lifted"
inferUse :: Use Desugared -> Contextual (Use Desugared, ValueType Desugared)
inferUse u@(Op x _) =        -- Var, PolyVar, Command rules
  do logBeginInferUse u
     ty <- find x
     res <- instantiate x ty
     logEndInferUse u res
     return (u, res)
inferUse app@(App f xs a) =  -- App rule
  do logBeginInferUse app
     (f', ty) <- inferUse f
     (xs', res) <- discriminate ty
     logEndInferUse app res
     return (App f' xs' a, res)
  where -- Case distinction on operator's type ty
        -- 1) ty is susp. comp. type
        --    - Check that required abilities of f are admitted (unify with amb)
        --    - Check typings of arguments x_i: p_i in [amb + adj_i] for all i
        -- 2) ty is flex. type var. y
        --    - f must have occured in context as one of these:
        --      2.1) [..., y:=?,   ..., f:=y, ...]
        --           y is not determined yet, create type of right shape
        --           (according to arguments) and constrain ty (unify)
        --      2.2) [..., y:=ty', ..., f:=y, ...]
        --           try 2) again, this time with ty'
        discriminate :: ValueType Desugared -> Contextual ([Term Desugared], ValueType Desugared)
        discriminate ty@(SCTy (CompType ps (Peg ab ty' _) _) _) =
        -- {p_1 -> ... p_n -> [ab] ty'}
          do amb <- getAmbient
             -- require ab = amb
             unifyAb ab amb
             -- Check typings of x_i for port p_i
             xs' <- zipWithM checkArg ps xs
             return (xs', ty')
        discriminate ty@(FTVar y a) =
          do mty <- findFTVar y  -- find definition of y in context
             case mty of
               Nothing -> -- 2.1)
                 -- TODO: check that this is correct
                 do addMark
                    amb <- getAmbient
                    ps <- mapM (\_ -> freshPort "X" a) xs
                    q@(Peg ab ty' _)  <- freshPegWithAb amb "Y" a
                    unify ty (SCTy (CompType ps q a) a)
                    -- TODO: LC: We have to check typings of x_i for port p_i?
                    -- (didn't appear as a bug yet, but should be examined/fixed eventually)
                    return (xs, ty')
                 -- errTy ty
               Just ty' -> discriminate ty' -- 2.2)
        discriminate ty = errTy ty

        -- TODO: tidy.
        -- We don't need to report an error here, but rather generate
        -- appropriate fresh type variables as above.
        errTy ty = throwError $
                   "application (" ++ show (App f xs (Desugared Generated)) ++
                   "): expected suspended computation but got " ++
                   show (ppValueType ty)

        -- Check typing tm: ty in ambient [adj]
        checkArg :: Port Desugared -> Term Desugared -> Contextual (Term Desugared)
        checkArg (Port adjs ty _) tm =
          do amb <- getAmbient >>= expandAb
             (_, amb') <- applyAllAdjustments adjs amb
             inAmbient amb' (checkTerm tm ty)
inferUse adpd@(Adapted adps t a) =
  do logBeginInferUse adpd
     amb <- getAmbient >>= expandAb
     let (Ab v p@(InterfaceMap m _) _) = amb
     -- Check that the adaptors can be performed and modify the ambient
     -- accordingly
     (adps', amb') <- applyAllAdaptors adps amb
     (t', res) <- inAmbient amb' (inferUse t)
     logEndInferUse adpd res
     return (Adapted adps' t' a, res)

-- 2nd major TC function besides "check": Check that term (construction) has
-- given type
checkTerm :: Term Desugared -> ValueType Desugared -> Contextual (Term Desugared)
checkTerm (SC sc a) ty = SC <$> checkSuspension sc ty <*> pure a
checkTerm tm@(StrTerm _ a) ty = unify (desugaredStrTy a) ty >> return tm
checkTerm tm@(IntTerm _ a) ty = unify (IntTy a) ty >> return tm
checkTerm tm@(CharTerm _ a) ty = unify (CharTy a) ty >> return tm
checkTerm tm@(TermSeq tm1 tm2 a) ty =
  -- create dummy mvar s.t. any type of tm1 can be unified with it
  do ftvar <- freshMVar "seq"
     tm1' <- checkTerm tm1 (FTVar ftvar a)
     tm2' <- checkTerm tm2 ty
     return $ TermSeq tm1' tm2' a
checkTerm (Use u a) t = do (u', s) <- inferUse u
                           unify t s
                           return $ Use u' a
checkTerm (DCon (DataCon k xs a') a) ty =
  do (dt, args, ts) <- getCtr k
     -- data dt arg_1 ... arg_m = k t_1 ... t_n | ...
     addMark
     -- prepare flexible ty vars and ty args
     args' <- mapM (makeFlexibleTypeArg []) args
     ts' <- mapM (makeFlexible []) ts
     -- unify with expected type
     unify ty (DTTy dt args' a)
     xs' <- zipWithM checkTerm xs ts'
     return $ DCon (DataCon k xs' a') a

-- Check that susp. comp. term has given type, corresponds to Comp rule
-- Case distinction on expected type:
-- 1) Check {cls_1 | ... | cls_m} : {p_1 -> ... -> p_n -> q}
-- 2) Check {cls_1 | ... | cls_m} : ty
--    - For each cls_i:
--      - Check against a type of the right shape (of fresh flex. var.s which
--        then get bound via checking
--      - Unify the obtained type for cls_i with overall type ty
checkSuspension :: Suspension Desugared -> ValueType Desugared -> Contextual (Suspension Desugared)               -- Comp rule
checkSuspension (Suspension xs a) (SCTy ty@(CompType ps q _) _) = do
  xs' <- mapM (checkCls ty) xs
  return (Suspension xs' a)
checkSuspension (Suspension xs a) ty = do
  xs' <- mapM (checkCls' ty) xs
  return (Suspension xs' a)
  where
    checkCls' :: ValueType Desugared -> Clause Desugared -> Contextual (Clause Desugared)
    checkCls' ty cls@(MkClause pats tm a) = do
      pushMarkCtx
      ps <- mapM (\_ -> freshPort "X" a) pats
      q <- freshPeg "E" "X" a
      -- {p_1 -> ... -> p_n -> q} for fresh flex. var.s ps, q
      let cty = CompType ps q a
      cls' <- checkCls cty cls     -- assign these variables
      unify ty (SCTy cty a)        -- unify with resulting ty
      purgeMarks
      return cls'

-- create port <i>X for fresh X
freshPort :: Identifier -> Desugared -> Contextual (Port Desugared)
freshPort x a = do ty <- FTVar <$> freshMVar x <*> pure a
                   return $ Port [] ty a

-- create peg [E|]Y for fresh E, Y
freshPeg :: Identifier -> Identifier -> Desugared -> Contextual (Peg Desugared)
freshPeg x y a = do v <- AbFVar <$> freshMVar x <*> pure a
                    ty <- FTVar <$> freshMVar y <*> pure a
                    return $ Peg (Ab v (InterfaceMap M.empty a) a) ty a

-- create peg [ab]X for given [ab], fresh X
freshPegWithAb :: Ab Desugared -> Identifier -> Desugared -> Contextual (Peg Desugared)
freshPegWithAb ab x a = do ty <- FTVar <$> freshMVar x <*> pure a
                           return $ Peg ab ty a

-- Check that given clause has given susp. comp. type (ports, peg)
checkCls :: CompType Desugared -> Clause Desugared ->
            Contextual (Clause Desugared)
checkCls (CompType ports (Peg ab ty _) _) cls@(MkClause pats tm a)
-- type:     port_1 -> ... -> port_n -> [ab]ty
-- clause:   pat_1     ...    pat_n  =  tm
  | length pats == length ports =
     do pushMarkCtx
        putAmbient ab  -- initialise ambient ability
        bs <- concat <$> zipWithM checkPat pats ports
        -- Bring any bindings in to scope for checking the term then purge the
        -- marks (and suffixes) in the context created for this clause.
        if null bs then -- Just purge marks
                        do tm' <- checkTerm tm ty
                           purgeMarks
                           return (MkClause pats tm' a)
                   else -- Push all bindings to context, then check tm, then
                        -- remove bindings, finally purge marks.
                        do tm' <- foldl1 (.) (map (uncurry inScope) bs) $ checkTerm tm ty
                           purgeMarks
                           return (MkClause pats tm' a)
  | otherwise = throwError $ errorTCPatternPortMismatch cls

-- Check that given pattern matches given port
checkPat :: Pattern Desugared -> Port Desugared -> Contextual [TermBinding]
checkPat (VPat vp _) (Port _ ty _) = checkVPat vp ty
checkPat (CmdPat cmd n xs g a) port@(Port adjs ty b) =                                  -- P-Request rule
-- interface itf q_1 ... q_m =
--   cmd r_1 ... r_l: t_1 -> ... -> t_n -> y | ...

-- port:     <itf p_1 ... p_m> ty
-- pattern:  <cmd x_1 ... x_n -> g>
  do (itf, qs, rs, ts, y) <- getCmd cmd
     -- how is itf instantiated in adj?
     let (insts, _) = adjsNormalForm adjs
     let insts' = bwd2fwd $ M.findWithDefault BEmp itf insts
     if length insts' > n then
       do let ps = insts' !! n
          addMark
          -- Flexible ty vars (corresponding to qs)
          skip <- getCmdTyVars cmd
          -- Localise qs, bind them to their instantiation
          -- (according to adjustment) and localise their occurences
          -- in ts, y
          qs' <- mapM (makeFlexibleTypeArg skip) qs
          ts' <- mapM (makeFlexible skip) ts
          y' <- makeFlexible skip y
          zipWithM_ unifyTypeArg ps qs'
          -- Check command patterns against spec. in interface def.
          bs <- concat <$> zipWithM checkVPat xs ts'
          -- type of continuation:  {y' -> [adj + currentAmb]ty}
          kty <- contType y' adjs ty a
          -- bindings: continuation + patterns
          return ((Mono g a, kty) : bs)
     else
       throwError $ errorTCCmdNotFoundInPort cmd n port
checkPat (ThkPat x a) (Port adjs ty b) =                                         -- P-CatchAll rule
-- pattern:  x
  do amb <- getAmbient
     (_, amb') <- applyAllAdjustments adjs amb
     return [(Mono x a, SCTy (CompType [] (Peg amb' ty b) b) b)]

-- continuation type
contType :: ValueType Desugared -> [Adjustment Desugared] -> ValueType Desugared -> Desugared ->
            Contextual (ValueType Desugared)
contType x adjs y a =
  do amb <- getAmbient
     (_, amb') <- applyAllAdjustments adjs amb
     return $ SCTy (CompType [Port [] x a] (Peg amb' y a) a) a

-- Check that a value pattern has a given type (corresponding to rules)
-- Return its bindings (id -> value type)
checkVPat :: ValuePat Desugared -> ValueType Desugared -> Contextual [TermBinding]
checkVPat (VarPat x a) ty = return [(Mono x a, ty)]                             -- P-Var rule
--         x
checkVPat (DataPat k ps a) ty =                                                 -- P-Data rule
--         k p_1 .. p_n
  do (dt, args, ts) <- getCtr k
--   data dt arg_1 .. arg_m = k t_1 .. t_n | ...
     addMark
     args' <- mapM (makeFlexibleTypeArg []) args
     ts' <- mapM (makeFlexible []) ts
     unify ty (DTTy dt args' a)
     concat <$> zipWithM checkVPat ps ts'
checkVPat (CharPat _ a) ty = unify ty (CharTy a) >> return []
checkVPat (StrPat _ a) ty = unify ty (desugaredStrTy a) >> return []
checkVPat (IntPat _ a) ty = unify ty (IntTy a) >> return []
-- checkVPat p ty = throwError $ "failed to match value pattern " ++
--                  (show p) ++ " with type " ++ (show ty)


-- Validate that the adaptors in the ports match the peg. Annotate the
-- adaptors in the ports accordingly via "applyAllAdjustments".
validateCompType :: CompType Desugared -> Contextual (CompType Desugared)
validateCompType (CompType ps q@(Peg ab ty a') a) = do
  ps' <- mapM validatePort ps
  return $ CompType ps' q a
  where
    validatePort :: Port Desugared -> Contextual (Port Desugared)
    validatePort (Port adjs ty a) = do
      (adjs', _) <- applyAllAdjustments adjs ab
      return $ Port adjs' ty a


-- Given a list of ids and a type as input, any rigid (val/eff) ty var
-- contained in ty which does *not* belong to the list is made flexible.
-- The context is thereby extended.
-- Case distinction over contained rigid (val/eff) ty var:
-- 1) it is already part of current locality (up to the Mark)
--    -> return its occuring name
-- 2) it is not part of current locality
--    -> create fresh name in context and return
makeFlexible :: [Identifier] -> ValueType Desugared -> Contextual (ValueType Desugared)
makeFlexible skip (DTTy id ts a) = DTTy id <$> mapM (makeFlexibleTypeArg skip) ts <*> pure a
makeFlexible skip (SCTy cty a) = SCTy <$> makeFlexibleCompType skip cty <*> pure a
makeFlexible skip (RTVar x a) | x `notElem` skip = FTVar <$> (getContext >>= find') <*> pure a
-- find' either creates a new FlexMVar in current locality or identifies the one
-- already existing
  where find' BEmp = freshMVar x
        find' (es :< FlexMVar y _) | trimVar x == trimVar y = return y
        find' (es :< Mark) = freshMVar x  -- only search in current locality
        find' (es :< _) = find' es
makeFlexible skip ty = return ty

makeFlexibleAb :: [Identifier] -> Ab Desugared -> Contextual (Ab Desugared)
makeFlexibleAb skip (Ab v (InterfaceMap m _) a) = case v of
  AbRVar x b -> do v' <- if x `notElem` skip then AbFVar <$> (getContext >>= find' x) <*> pure b else return $ AbRVar x b
                   m' <- mapM (mapM (mapM (makeFlexibleTypeArg skip))) m
                   return $ Ab v' (InterfaceMap m' a) a
  _ ->          do m' <- mapM (mapM (mapM (makeFlexibleTypeArg skip))) m
                   return $ Ab v (InterfaceMap m' a) a
-- find' either creates a new FlexMVar in current locality or identifies the one
-- already existing
  where find' x BEmp = freshMVar x
        find' x (es :< FlexMVar y _) | trimVar x == trimVar y = return y
        find' x (es :< Mark) = freshMVar x
        find' x (es :< _) = find' x es

makeFlexibleTypeArg :: [Identifier] -> TypeArg Desugared -> Contextual (TypeArg Desugared)
makeFlexibleTypeArg skip (VArg t a)  = VArg <$> makeFlexible skip t <*> pure a
makeFlexibleTypeArg skip (EArg ab a) = EArg <$> makeFlexibleAb skip ab <*> pure a

makeFlexibleAdj :: [Identifier] -> Adjustment Desugared -> Contextual (Adjustment Desugared)
makeFlexibleAdj skip (ConsAdj x ts a) = do ts' <- mapM (makeFlexibleTypeArg skip) ts
                                           return $ ConsAdj x ts' a
makeFlexibleAdj skip (AdaptorAdj adp a) = return $ AdaptorAdj adp a

makeFlexibleCompType :: [Identifier] -> CompType Desugared -> Contextual (CompType Desugared)
makeFlexibleCompType skip (CompType ps q a) =
  CompType
  <$> mapM (makeFlexiblePort skip) ps
  <*> makeFlexiblePeg skip q
  <*> pure a

makeFlexiblePeg :: [Identifier] -> Peg Desugared -> Contextual (Peg Desugared)
makeFlexiblePeg skip (Peg ab ty a) = Peg <$>
                                      makeFlexibleAb skip ab <*>
                                      makeFlexible skip ty <*>
                                      pure a

makeFlexiblePort :: [Identifier] -> Port Desugared -> Contextual (Port Desugared)
makeFlexiblePort skip (Port adjs ty a) =
  Port <$> mapM (makeFlexibleAdj skip) adjs
       <*> makeFlexible skip ty
       <*> pure a

applyAllAdjustments :: [Adjustment Desugared] -> Ab Desugared ->
                       Contextual ([Adjustment Desugared], Ab Desugared)
applyAllAdjustments [] ab = return ([], ab)

applyAllAdjustments (adj@(ConsAdj x ts _) : adjr) (Ab v p@(InterfaceMap m a') a) = do
  let ab' = Ab v (InterfaceMap (adjustWithDefault (:< ts) x BEmp m) a') a
  (adjr', ab'') <- applyAllAdjustments adjr ab'
  return (adj : adjr', ab'')

applyAllAdjustments (AdaptorAdj adp a : adjr) ab = do
  let mAdpAb = applyAdaptor adp ab
  case mAdpAb of
   Just (adp', ab') -> do
     (adjr'', ab'') <- applyAllAdjustments adjr ab'
     return (AdaptorAdj adp' a : adjr'', ab'')
   Nothing -> throwError $ errorAdaptor adp ab

applyAdaptor :: Adaptor Desugared -> Ab Desugared -> Maybe (Adaptor Desugared, Ab Desugared)
applyAdaptor adp ab@(Ab v p@(InterfaceMap m a') a) =
  case adpToCompilableAdp ab adp of
    Nothing -> Nothing
    Just adp'@(CompilableAdp x m' ns a'') ->
      let instances = (reverse . bwd2fwd) (M.findWithDefault BEmp x m) in
      let instances' = map (instances !!) ns in
      if null instances' then
        Just (adp', Ab v (InterfaceMap (M.delete x m) a') a)
      else
        Just (adp', Ab v (InterfaceMap (
          M.insert x ((fwd2bwd . reverse) instances') m
        ) a') a)

adpToCompilableAdp :: Ab Desugared -> Adaptor Desugared -> Maybe (Adaptor Desugared)
adpToCompilableAdp (Ab v p@(InterfaceMap m a') a) adp@(Adp x mm ns a'') =
  let instancesLength = (length . bwd2fwd) (M.findWithDefault BEmp x m) in
  if null ns || instancesLength > maximum ns then
    -- ns is only the xiferp (reverse prefix)
    -- now compute the liat (reverse tail)
    let liat = case mm of
                 Nothing -> []
                 (Just jm) -> reverse [jm .. instancesLength - 1] in
    let ns' = liat ++ ns in
    Just $ CompilableAdp x instancesLength ns' a''
  else Nothing
adpToCompilableAdp (Ab v p@(InterfaceMap m a') a) adp@(CompilableAdp x m' ns a'') =
  let instancesLength = (length . bwd2fwd) (M.findWithDefault BEmp x m) in
  if instancesLength == m' then Just adp else Nothing

applyAllAdaptors :: [Adaptor Desugared] -> Ab Desugared -> Contextual ([Adaptor Desugared], Ab Desugared)
applyAllAdaptors adps ab = do
  -- TODO: LC: kind of not nice, to wrap and then unwrap - implement
  -- differently later?
  let adjs = map (\adp -> AdaptorAdj adp (Desugared Generated)) adps
  (adjs', ab') <- applyAllAdjustments adjs ab
  let adps' = map unwrap adjs'
  return (adps', ab')
  where unwrap :: Adjustment Desugared -> Adaptor Desugared
        unwrap (AdaptorAdj adp _) = adp
        unwrap (ConsAdj _ _ _)    = error "invariant broken"
{-# ANN applyAllAdaptors "HLint: ignore Use record patterns" #-}

-- helpers

getCtr :: Identifier -> Contextual (Identifier, [TypeArg Desugared], [ValueType Desugared])
getCtr k = get >>= \s -> case M.lookup k (ctrMap s) of
  Nothing -> throwError $ errorTCNotACtr k
  Just (dt, ts, xs) -> return (dt, ts, xs)
