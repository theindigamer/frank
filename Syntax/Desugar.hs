-- Transform all type variables to unique rigid type variables.
module Syntax.Desugar where

import Control.Monad.State
import Control.Monad.Identity
import qualified Data.Map.Strict as M

import BwdFwd
import Syntax
import FreshNames

import Shonky.Renaming

type Desugar = StateT DState (FreshMT Identity)

type IdTVMap = M.Map Identifier (ValueType Desugared)

type IdAbModMap = M.Map Identifier (AbMod Desugared)

data DState = MkDState { env :: IdTVMap
                       , abModEnv :: IdAbModMap }

getDState :: Desugar DState
getDState = get

putDState :: DState -> Desugar ()
putDState = put

freshRTVar :: Identifier -> Desugared -> Desugar (ValueType Desugared)
freshRTVar x a = do n <- fresh
                    return $ RTVar (x ++ "$r" ++ show n) a

freshRigid :: Identifier -> Desugar Identifier
freshRigid x = do n <- fresh
                  return $ x ++ "$r" ++ show n

pullIdentifier :: ValueType Desugared -> Identifier
pullIdentifier (RTVar ident _) = ident
pullIdentifier _ = error "pullIdentifier called on something other than a rigid tvar"

putEnv :: IdTVMap -> Desugar ()
putEnv p = do s <- getDState
              putDState $ s { env = p }

getEnv :: Desugar IdTVMap
getEnv = env <$> getDState

putAbModEnv :: IdAbModMap -> Desugar ()
putAbModEnv p = do s <- getDState
                   putDState $ s { abModEnv = p }

getAbModEnv :: Desugar IdAbModMap
getAbModEnv = abModEnv <$> getDState

initDState :: DState
initDState = MkDState M.empty M.empty

desugar :: Program Refined -> Program Desugared
desugar (MkProgram xs) = MkProgram $ evalFresh m
  where m = evalStateT (mapM desugarTopTerm' xs) initDState
        desugarTopTerm' tm =
          do putEnv M.empty -- purge mappings from previous context.
             desugarTopTerm tm

-- no explicit refinements
desugarTopTerm :: TopTerm Refined -> Desugar (TopTerm Desugared)
desugarTopTerm (DataTerm dt a) = DataTerm <$> desugarDataType dt <*> pure (refToDesug a)
desugarTopTerm (InterfaceTerm itf a) = InterfaceTerm <$> desugarInterface itf <*> pure (refToDesug a)
desugarTopTerm (DefTerm def a) = DefTerm <$> desugarMultiHandlerDefinition def <*> pure (refToDesug a)

-- explicit refinements:
-- + type variables get fresh ids
desugarDataType :: DataType Refined -> Desugar (DataType Desugared)
desugarDataType (MkDataType dt ps ctrs a) = do
  -- id val & eff ty vars constructors
  -- generate fresh ids for ty vars
  xs' <- mapM (freshRigid . fst) ps
  -- map old value type variables to fresh ones
  putEnv $ M.fromList [(x, RTVar x' a') | ((x, VT), x') <- zip ps xs']
  -- map old effect type variables to fresh ones
  putAbModEnv $ M.fromList [(x, AbRVar x' a') | ((x, ET), x') <- zip ps xs']
  -- [(new var name, val or eff)]
  let ps' = [(x', k) | ((_, k), x') <- zip ps xs']
   -- the following will only use but not modify the DState
  ctrs' <- mapM desugarCtr ctrs
  -- ps' contains new fresh names
  return $ MkDataType dt ps' ctrs' a'
  where a' = refToDesug a

-- explicit refinements:
-- + type variables get fresh ids
desugarInterface :: Interface Refined -> Desugar (Interface Desugared)
desugarInterface (MkInterface itf ps cmds a) = do
  -- generate fresh ids for type variables
  xs' <- mapM (freshRigid . fst) ps
  let env' = M.fromList [(x, RTVar x' a') | ((x, VT), x') <- zip ps xs']        -- map old value type variables to fresh ones
  let abModEnv' = M.fromList [(x, AbRVar x' a') | ((x, ET), x') <- zip ps xs']  -- map old effect type variables to fresh ones
  -- [(new var name, val or eff)]
  let ps' = [(x', k) | ((_, k), x') <- zip ps xs']
  -- before desugaring each cmd, we need to reset the env
  cmds' <- mapM (\c -> do putEnv env'
                          putAbModEnv abModEnv'
                          desugarCmd c)
                cmds
  -- reset afterwards, too
  putEnv env'
  putAbModEnv abModEnv'
  return $ MkInterface itf ps' cmds' a'
  where a' = refToDesug a

-- no explicit refinements
desugarMultiHandlerDefinition :: MultiHandlerDefinition Refined -> Desugar (MultiHandlerDefinition Desugared)
desugarMultiHandlerDefinition (MkDef hdr ty xs a) = do
  ty' <- desugarCompType ty
  xs' <- mapM desugarClause xs
  return $ MkDef hdr ty' xs' (refToDesug a)

-- explicit refinements:
-- + type variables get fresh ids
desugarCmd :: Cmd Refined -> Desugar (Cmd Desugared)
desugarCmd (Cmd cmd  ps                 xs       y a) = do
  --  id   val & eff ty vars  arg tys  return ty
  -- generate fresh ids for type variables
  ps' <- mapM (freshRigid . fst) ps
  -- map old value type variables to fresh ones
  putEnv $ M.fromList [(p, RTVar p' a') | ((p, VT), p') <- zip ps ps']
  -- map old effect type variables to fresh ones
  putAbModEnv $ M.fromList [(p, AbRVar p' a') | ((p, ET), p') <- zip ps ps']
  -- [(new var name, val or eff)]
  let ps'' = [(p', k) | ((_, k), p') <- zip ps ps']
  xs' <- mapM desugarValueType xs
  y' <- desugarValueType y
  return $ Cmd cmd ps'' xs' y' a'
  where a' = refToDesug a

-- no explicit refinements
desugarCtr :: Ctr Refined -> Desugar (Ctr Desugared)
desugarCtr (Ctr ctr xs a) = do
  xs' <- mapM desugarValueType xs
  return $ Ctr ctr xs' (refToDesug a)

-- explicit refinements:
-- + replace val ty vars by corresponding MkRTVar's of env,
--   generate new fresh one and add if not in env yet
-- + replace 'String' by 'List Char'
desugarValueType :: ValueType Refined -> Desugar (ValueType Desugared)
desugarValueType (TVar x a) =
  do env <- getEnv
     case M.lookup x env of
       Nothing -> do ty <- freshRTVar x (refToDesug a)
                     putEnv $ M.insert x ty env
                     return ty
       Just ty -> return ty
desugarValueType (DTTy dt ts a) = do
  ts' <- mapM desugarTypeArg ts
  return $ DTTy dt ts' (refToDesug a)
desugarValueType (SCTy ty a) = do
  ty' <- desugarCompType ty
  return $ SCTy ty' (refToDesug a)
-- replace 'String' by 'List Char'
desugarValueType (StringTy a) = return $ desugaredStrTy (refToDesug a)
desugarValueType (IntTy a) = return $ IntTy (refToDesug a)
desugarValueType (CharTy a) = return $ CharTy (refToDesug a)

-- nothing happens on this level
desugarTypeArg :: TypeArg Refined -> Desugar (TypeArg Desugared)
desugarTypeArg (VArg t a) = VArg <$> desugarValueType t <*> pure (refToDesug a)
desugarTypeArg (EArg ab a) = EArg <$> desugarAb ab <*> pure (refToDesug a)

-- nothing happens on this level
desugarCompType :: CompType Refined -> Desugar (CompType Desugared)
desugarCompType (CompType ports peg a) =
  CompType <$> mapM desugarPort ports <*> desugarPeg peg <*> pure (refToDesug a)

desugarPort :: Port Refined -> Desugar (Port Desugared)
desugarPort (Port adjs ty a) = Port <$> mapM desugarAdjustment adjs
                                    <*> desugarValueType ty
                                    <*> pure (refToDesug a)

-- nothing happens on this level
desugarPeg :: Peg Refined -> Desugar (Peg Desugared)
desugarPeg (Peg ab ty a) = Peg <$> desugarAb ab <*> desugarValueType ty <*> pure (refToDesug a)

-- nothing happens on this level
desugarAb :: Ab Refined -> Desugar (Ab Desugared)
desugarAb (Ab v itfMap a) = Ab <$> desugarAbMod v <*> desugarInterfaceMap itfMap <*> pure (refToDesug a)

-- explicit desugaring:
-- + replace effect type variables by corresponding MkAbRVar's of abModEnv,
--   generate new fresh one and add if not in env yet
desugarAbMod :: AbMod Refined -> Desugar (AbMod Desugared)
desugarAbMod (EmpAb a) = return $ EmpAb (refToDesug a)
desugarAbMod (AbVar x a) =
  do env <- getAbModEnv
     case M.lookup x env of
       Nothing -> do n <- fresh
                     let var = AbRVar (x ++ "$r" ++ show n) (refToDesug a)
                     putAbModEnv $ M.insert x var env
                     return var
       Just var -> return var

-- nothing happens on this level
desugarAdjustment :: Adjustment Refined -> Desugar (Adjustment Desugared)
desugarAdjustment (ConsAdj x ts a) = ConsAdj x <$> mapM desugarTypeArg ts <*> pure (refToDesug a)
desugarAdjustment (AdaptorAdj adp a) = AdaptorAdj <$> desugarAdaptor adp <*> pure (refToDesug a)

desugarInterfaceMap :: InterfaceMap Refined -> Desugar (InterfaceMap Desugared)
desugarInterfaceMap (InterfaceMap m a) = do
  m' <- mapM (mapM (mapM desugarTypeArg)) m
  return $ InterfaceMap m' (refToDesug a)

-- no explicit desugaring: clauses (and constituents) unaffected between
-- Refine/Desugar phase
desugarClause :: Clause Refined -> Desugar (Clause Desugared)
desugarClause (MkClause ps tm a) = do
  ps' <- mapM desugarPattern ps
  tm' <- desugarTerm tm
  return $ MkClause ps' tm' (refToDesug a)

desugarTerm :: Term Refined -> Desugar (Term Desugared)
desugarTerm (SC x a) = SC <$> desugarSuspension x <*> pure (refToDesug a)
desugarTerm (StrTerm s a) = return $ StrTerm s (refToDesug a)
desugarTerm (IntTerm n a) = return $ IntTerm n (refToDesug a)
desugarTerm (CharTerm c a) = return $ CharTerm c (refToDesug a)
desugarTerm (TermSeq tm1 tm2 a) = TermSeq <$> desugarTerm tm1 <*> desugarTerm tm2 <*> pure (refToDesug a)
desugarTerm (Use u a) = Use <$> desugarUse u <*> pure (refToDesug a)
desugarTerm (DCon d a) = DCon <$> desugarDCon d <*> pure (refToDesug a)

desugarPattern :: Pattern Refined -> Desugar (Pattern Desugared)
desugarPattern (VPat v a) = VPat <$> desugarVPat v <*> pure (refToDesug a)
desugarPattern (CmdPat c n vs k a) = do vs' <- mapM desugarVPat vs
                                        return $ CmdPat c n vs' k
                                                        (refToDesug a)
desugarPattern (ThkPat x a) = return $ ThkPat x (refToDesug a)

desugarVPat :: ValuePat Refined -> Desugar (ValuePat Desugared)
desugarVPat (VarPat x a) = return $ VarPat x (refToDesug a)
desugarVPat (DataPat x xs a) =
  DataPat x <$> mapM desugarVPat xs <*> pure (refToDesug a)
desugarVPat (IntPat i a) = return $ IntPat i (refToDesug a)
desugarVPat (CharPat c a) = return $ CharPat c (refToDesug a)
desugarVPat (StrPat s a) = return $ StrPat s (refToDesug a)

desugarSuspension :: Suspension Refined -> Desugar (Suspension Desugared)
desugarSuspension (Suspension xs a) =
  Suspension <$> mapM desugarClause xs <*> pure (refToDesug a)

desugarUse :: Use Refined -> Desugar (Use Desugared)
desugarUse (App use xs a) =
  App <$> desugarUse use <*> mapM desugarTerm xs <*> pure (refToDesug a)
desugarUse (Op op a) = Op <$> desugarOperator op <*> pure (refToDesug a)
desugarUse (Adapted rs t a) =
  Adapted <$> mapM desugarAdaptor rs <*> desugarUse t <*> pure (refToDesug a)

-- explicit refinements:
-- + Rem, Copy and Swap gets desugared to GeneralAdaptor
desugarAdaptor :: Adaptor Refined -> Desugar (Adaptor Desugared)
desugarAdaptor (Adp x ns k a) = return $ Adp x ns k (refToDesug a)

desugarOperator :: Operator Refined -> Desugar (Operator Desugared)
desugarOperator (Mono x a) = return $ Mono x (refToDesug a)
desugarOperator (Poly x a) = return $ Poly x (refToDesug a)
desugarOperator (CmdIdentifier x a) = return $ CmdIdentifier x (refToDesug a)

desugarDCon :: DataCon Refined -> Desugar (DataCon Desugared)
desugarDCon (DataCon id xs a) =
  DataCon id <$> mapM desugarTerm xs <*> pure (refToDesug a)

-- Helpers

refToDesug :: Refined -> Desugared
refToDesug (Refined loc) = Desugared loc
