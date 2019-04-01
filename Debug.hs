-- Specifies communication with user: Debugging, Error reporting, ...
{-# LANGUAGE GADTs #-}
module Debug where

import Prelude hiding ((<>))

import BwdFwd
import Syntax
import ParserCommon
import Syntax.Refine.Common
import TypeCheck.Common
import qualified Syntax.AbilityMode as AbilityMode
import qualified Syntax.Adaptor as Adaptor

import Control.Monad
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.List

import Debug.Trace

import Data.IORef
import System.IO.Unsafe

import Shonky.Syntax
import Shonky.Renaming

import qualified Text.PrettyPrint as PP

-- Is set by the main entry point if relevant flag detected.
-- 1) isDebugVerboseOn
-- 2) isDebugParserOn
-- 3) isDebugTypeCheckOn
debugMode :: IORef (Bool, Bool, Bool)
{-# NOINLINE debugMode #-}
debugMode = unsafePerformIO (newIORef (False, False, False))

-- Hack: Use () argument to prevent caching
getDebugMode :: () -> (Bool, Bool, Bool)
{-# NOINLINE getDebugMode #-}
getDebugMode () = unsafePerformIO (readIORef debugMode)

-- Output full (untrimmed) ty var names
-- Hack: Use () argument to prevent caching
isDebugVerboseOn :: () -> Bool
isDebugVerboseOn () = case getDebugMode () of (b, _, _) -> b

-- Output parsing process
-- Hack: Use () argument to prevent caching
isDebugParserOn :: () -> Bool
isDebugParserOn () = case getDebugMode () of (_, b, _) -> b

-- Output type checking process
-- Hack: Use () argument to prevent caching
isDebugTypeCheckOn :: () -> Bool
isDebugTypeCheckOn () = case getDebugMode () of (_, _, b) -> b

ifDebugTypeCheckOnThen :: Contextual () -> Contextual ()
ifDebugTypeCheckOnThen = when (isDebugTypeCheckOn ())

{- Error messages (only producing the output strings) -}

errorRefNoMainFunction :: String
errorRefNoMainFunction = "no main function defined"

errorRefDuplParamData :: DataType Raw -> String
errorRefDuplParamData dt@(MkDataType x _ _ _) = "duplicate parameter in datatype " ++ x ++ " (" ++ show (ppSourceOf dt) ++ ")"

errorRefDuplParamInterface :: Interface Raw -> String
errorRefDuplParamInterface itf@(MkInterface x _ _ _) =
  "duplicate parameter in interface " ++ x ++ " (" ++ show (ppSourceOf itf) ++ ")"

errorRefDuplParamInterfaceAl :: InterfaceAlias Raw -> String
errorRefDuplParamInterfaceAl itfAl@(MkInterfaceAlias x _ _ _) =
  "duplicate parameter in interface alias " ++ x ++ " (" ++ show (ppSourceOf itfAl) ++ ")"

errorRefDuplParamCmd :: Cmd Raw -> String
errorRefDuplParamCmd cmd@(Cmd x _ _ _ _) = "duplicate parameter in command " ++ x ++ " (" ++ show (ppSourceOf cmd) ++ ")"

errorRefAbMultEffVars :: Ability Raw -> [Identifier] -> String
errorRefAbMultEffVars ab@(MkAbility v m a) es = "ability has multiple effect variables " ++ show es ++ " (" ++ show (ppSourceOf ab) ++ ")"

errorRefEffVarNoParams :: Identifier -> String
errorRefEffVarNoParams x = "effect variable " ++ x ++ " may not take parameters"

errorRefIdNotDeclared :: String -> Identifier -> Raw -> String
errorRefIdNotDeclared sort x a = "no " ++ sort ++ " named " ++ x ++ " declared (" ++ show (ppSourceOf a) ++ ")"

errorRefExpectedUse :: Term Refined -> String
errorRefExpectedUse tm = "expected use but got term: " ++ show tm ++ "(" ++ show (ppSourceOf tm) ++ ")"

errorRefEntryAlreadyDefined :: String -> Identifier -> String
errorRefEntryAlreadyDefined sort x = sort ++ " " ++ x ++ " already defined"

errorRefDuplTopTerm :: String -> Identifier -> Source -> String
errorRefDuplTopTerm sort x a = "duplicate " ++ sort ++ ": " ++ x ++ " already defined (" ++ show a ++ ")"

errorRefNumberOfArguments :: Identifier -> Int -> Int -> Raw -> String
errorRefNumberOfArguments x exp act a = x ++ " expects " ++ show exp ++ " argument(s) but " ++ show act ++ " given (" ++ show (ppSourceOf a) ++ ")"

errorRefInterfaceAlCycle :: Identifier -> String
errorRefInterfaceAlCycle x = "interface alias " ++ show x ++ " is defined in terms of itself (cycle)"

errorTCNotInScope :: Operator Desugared -> String
errorTCNotInScope op = "'" ++ getOpName op ++ "' not in scope (" ++ show (ppSourceOf op) ++ ")"

errorTCPatternPortMismatch :: Clause Desugared -> String
errorTCPatternPortMismatch cls = "number of patterns not equal to number of ports (" ++ show (ppSourceOf cls) ++ ")"

errorTCCmdNotFoundInPort :: Identifier -> Int -> Port Desugared -> String
errorTCCmdNotFoundInPort cmd n port = "command " ++ cmd ++ "." ++ show n ++ " not found in adjustments of port " ++ show (ppPort port) ++ " (" ++ show (ppSourceOf port) ++ ")"

errorTCNotACtr :: Identifier -> String
errorTCNotACtr x = "'" ++ x ++ "' is not a constructor"

errorUnifDiffNumberArgs :: ValueType Desugared -> ValueType Desugared -> String
errorUnifDiffNumberArgs v1 v2 =
  "failed to unify " ++ show (ppValueType v1) ++ " (" ++ show (ppSourceOf v1) ++ ") with " ++ show (ppValueType v2) ++ " (" ++ show (ppSourceOf v2) ++ ")" ++ " because they have different numbers of type arguments"

errorUnifTys :: ValueType Desugared -> ValueType Desugared -> String
errorUnifTys t1 t2 =
  "failed to unify " ++ show (ppValueType t1) ++ " (" ++ show (ppSourceOf t1) ++ ") with " ++ show (ppValueType t2) ++ " (" ++ show (ppSourceOf t2) ++ ")"

errorUnifTypeArgs :: TypeArg Desugared -> TypeArg Desugared -> String
errorUnifTypeArgs t1 t2 =
  "failed to unify type arguments " ++ show (ppTypeArg t1) ++ " (" ++ show (ppSourceOf t1) ++ ")" ++ " with " ++ show (ppTypeArg t2) ++ " (" ++ show (ppSourceOf t2) ++ ")"

errorUnifAbs :: Ability Desugared -> Ability Desugared -> String
errorUnifAbs ab1 ab2 =
  "cannot unify abilities " ++ show (ppAb ab1) ++ " (" ++ show (ppSourceOf ab1) ++ ")" ++ " and " ++ show (ppAb ab2) ++ " (" ++ show (ppSourceOf ab2) ++ ")"

errorUnifInterfaceMaps :: InterfaceMap Desugared -> InterfaceMap Desugared -> String
errorUnifInterfaceMaps m1 m2 =
  "cannot unify interface maps " ++ show (ppInterfaceMap m1) ++ " (" ++ show (ppSourceOf m1) ++ ")" ++ " and " ++ show (ppInterfaceMap m2) ++ " (" ++ show (ppSourceOf m2) ++ ")"

errorAdaptor :: Adaptor Desugared -> Ability Desugared -> String
errorAdaptor adpd@(Adaptor.Adp x ns k _) ab =
  "Adaptor " ++ show (ppAdaptor adpd) ++
  " is not a valid adaptor in ambient " ++ show (ppAb ab) ++
  " (" ++  show (ppSourceOf adpd) ++ ")"
errorAdaptor adpd@(Adaptor.Compilable x m ns _) ab =
  "Adaptor " ++ show (ppAdaptor adpd) ++
  " is not a valid adaptor in ambient " ++ show (ppAb ab) ++
  " (" ++  show (ppSourceOf adpd) ++ ")"

errorUnifSolveOccurCheck :: String
errorUnifSolveOccurCheck = "solve: occurs check failure"

errorFindCmdNotPermit :: String -> Desugared -> String -> Ability Desugared -> String
errorFindCmdNotPermit cmd loc itf amb = "command " ++ cmd ++ " belonging to interface " ++ itf ++ " not permitted by ambient ability: " ++ show (ppAb amb) ++ " (" ++ show (ppSourceOf amb) ++ ")"

{- Logging (output if debug mode is on) -}

logBeginFindCmd :: Identifier -> Identifier -> Maybe [TypeArg Desugared] -> Contextual ()
logBeginFindCmd x itf mps = ifDebugTypeCheckOnThen $
  debugTypeCheckM $ "find command " ++ show x ++ " of interface " ++ show itf ++
                    " with instantiation " ++ show (mps >>= Just . map (show . ppTypeArg)) ++ "\n\n"

logEndFindCmd :: Identifier -> ValueType Desugared -> Contextual ()
logEndFindCmd x ty = ifDebugTypeCheckOnThen $
  debugTypeCheckM $ "ended find command " ++ show x ++ ", resulting type is: " ++
                    show (ppValueType ty)

logBeginInferUse :: Use Desugared -> Contextual ()
logBeginInferUse u@(Op x _) = ifDebugTypeCheckOnThen $ do
  amb <- getAmbient
  debugTypeCheckM $ "begin infer use of single: Under curr. amb. " ++ show (ppAb amb) ++ "\n   infer type of " ++ show (ppUse u) ++ "\n\n"
  ctx <- getContext
  debugTypeCheckM ("cur. context is:\n" ++ show (ppContext ctx) ++ "\n\n")
logBeginInferUse u@(App f xs _) = ifDebugTypeCheckOnThen $ do
  amb <- getAmbient
  debugTypeCheckM $ "begin infer use of app: Under curr. amb. " ++ show (ppAb amb) ++ "\n   infer type of " ++ show (ppUse u) ++ "\n\n"
logBeginInferUse u@(Adapted rs t _) = ifDebugTypeCheckOnThen $ do
  amb <- getAmbient
  debugTypeCheckM $ "begin infer use of app: Under curr. amb. " ++ show (ppAb amb) ++ "\n   infer type of " ++ show (ppUse u) ++ "\n\n"


logEndInferUse :: Use Desugared -> ValueType Desugared -> Contextual ()
logEndInferUse u@(Op x _) ty = ifDebugTypeCheckOnThen $ do
  amb <- getAmbient
  debugTypeCheckM $ "ended infer use of single: Under curr. amb. " ++ show (ppAb amb) ++ "\n   infer type of " ++ show (ppUse u) ++ "\n   gives " ++ show (ppValueType ty)
  ctx <- getContext
  debugTypeCheckM ("cur. context is:\n" ++ show (ppContext ctx) ++ "\n\n")
logEndInferUse u@(App f xs _) ty = ifDebugTypeCheckOnThen $ do
  amb <- getAmbient
  debugTypeCheckM $ "ended infer use of app: Under curr. amb. " ++ show (ppAb amb) ++ "\n   infer type of " ++ show (ppUse u) ++ "\n   gives " ++ show (ppValueType ty) ++ "\n\n"
logEndInferUse u@(Adapted rs t _) ty = ifDebugTypeCheckOnThen $ do
  amb <- getAmbient
  debugTypeCheckM $ "ended infer use of redirected: Under curr. amb. " ++
    show (ppAb amb) ++ " redirected by <" ++ show rs ++
    ">\n   infer type of " ++ show (ppUse u) ++
    "\n   gives " ++ show (ppValueType ty) ++ "\n\n"

logBeginUnify :: ValueType Desugared -> ValueType Desugared -> Contextual ()
logBeginUnify t0 t1 = ifDebugTypeCheckOnThen $ do
  ctx <- getContext
  debugTypeCheckM $ "begin to unify\n   " ++ show (ppValueType t0) ++ "\nwith\n   " ++ show (ppValueType t1) ++ "\nCurrent context:\n" ++ show (ppContext ctx) ++ "\n\n"

logEndUnify :: ValueType Desugared -> ValueType Desugared -> Contextual ()
logEndUnify t0 t1 = ifDebugTypeCheckOnThen $ do
  ctx <- getContext
  debugTypeCheckM $ "ended unifying\n   " ++ show (ppValueType t0) ++ "\nwith\n   " ++ show (ppValueType t1) ++ "\nCurrent context:\n" ++ show (ppContext ctx) ++ "\n\n"

logBeginUnifyAb :: Ability Desugared -> Ability Desugared -> Contextual ()
logBeginUnifyAb ab0 ab1 = ifDebugTypeCheckOnThen $ do
  ctx <- getContext
  debugTypeCheckM $ "begin to unify ab. \n   " ++ show (ppAb ab0) ++ "\nwith\n   " ++ show (ppAb ab1) ++ "\nCurrent context:\n" ++ show (ppContext ctx) ++ "\n\n"

logEndUnifyAb :: Ability Desugared -> Ability Desugared -> Contextual ()
logEndUnifyAb ab0 ab1 = ifDebugTypeCheckOnThen $ do
  ctx <- getContext
  debugTypeCheckM $ "ended unifying ab. \n   " ++ show (ppAb ab0) ++ "\nwith\n   " ++ show (ppAb ab1) ++ "\nCurrent context:\n" ++ show (ppContext ctx) ++ "\n\n"

logBeginSolve :: Identifier -> Suffix -> ValueType Desugared -> Contextual ()
logBeginSolve a ext ty = ifDebugTypeCheckOnThen $ do
  ctx <- getContext
  debugTypeCheckM $ "begin to solve " ++ show a ++ " = " ++ show (ppValueType ty) ++ "\n under suffix\n   " ++ show (ppSuffix ext) ++ "\n\n"

logSolveStep :: (Bool, Bool, Decl) -> Contextual ()
logSolveStep p = ifDebugTypeCheckOnThen $ do
  ctx <- getContext
  debugTypeCheckM "solving step: "
  case p of
    (_,     _,     TyDefn bty) -> debugTypeCheckM "\"inst-subs\""
    (True,  True,  Hole)       -> return ()
    (True,  False, Hole)       -> debugTypeCheckM "\"inst-define\""
    (False, True,  _)          -> debugTypeCheckM "\"inst-depend\""
    (False, False, d)          -> debugTypeCheckM $ "\"inst-skip-ty\", decl=" ++ show d
    (_,     _,     AbDefn _)   -> return ()
  debugTypeCheckM $ "current context:\n" ++ show (ppContext ctx) ++ "\n\n"

logEndSolve :: Identifier -> Suffix -> ValueType Desugared -> Contextual ()
logEndSolve a ext ty = ifDebugTypeCheckOnThen $ do
  ctx <- getContext
  debugTypeCheckM $ "ended solving " ++ show a ++ " = " ++ show (ppValueType ty) ++ "\n under suffix\n   " ++ show (ppSuffix ext) ++ "\n\n"

-- logBeginSolveForEVar :: Identifier -> Suffix -> ValueType Desugared -> Contextual ()
-- logBeginSolve a ext ty = ifDebugTypeCheckOnThen $ do
--   ctx <- getContext
--   debugTypeCheckM $ "begin to solve " ++ show a ++ " = " ++ show (ppValueType ty) ++ "\n under suffix\n   " ++ show (ppSuffix ext) ++ "\n\n"
--
-- logEndSolveForEVar :: Identifier -> Suffix -> ValueType Desugared -> Contextual ()
-- logEndSolve a ext ty = ifDebugTypeCheckOnThen $ do
--   ctx <- getContext
--   debugTypeCheckM $ "ended solving " ++ show a ++ " = " ++ show (ppValueType ty) ++ "\n under suffix\n   " ++ show (ppSuffix ext) ++ "\n\n"

debugParserM :: (MonadicParsing m) => String -> m ()
debugParserM = traceM

debugRefineM :: String -> Refine ()
debugRefineM = traceM

debugRefine :: String -> a -> a
debugRefine = trace

-- Uses the hack of of first retrieving context but without printing it.
-- This achieves that calls of this function are not cached and newly executed
-- every time.
debugTypeCheckM :: String -> Contextual ()
debugTypeCheckM str = do
  cxt <- getContext
  seq (ppContext cxt) traceM str

debugM :: (Monad m) => String -> m ()
debugM = traceM

{- Syntax pretty printers -}

(<+>) = (PP.<+>)
(<>) = (PP.<>)
($$) = (PP.$$)
($+$) = (PP.$+$)
text = PP.text
sep = PP.sep
nest = PP.nest
vcat = PP.vcat
hcat = PP.hcat
hsep = PP.hsep
colon = PP.colon
comma = PP.comma
empty = PP.empty
int = PP.int
punctuate = PP.punctuate
semi = PP.semi
rbrack = PP.rbrack
lbrack = PP.lbrack
doubleQuotes = PP.doubleQuotes
ppBrackets = PP.brackets
ppParens = PP.parens
ppChar = PP.char
vsep :: [PP.Doc] -> PP.Doc
vsep = foldr ($+$) empty

type Doc = PP.Doc

ppProgram :: (Show a, HasSource a) => Program a -> PP.Doc
ppProgram (MkProgram tts) = foldl (PP.$+$ ) PP.empty (map ppTopTerm tts)

ppTopTerm :: (Show a, HasSource a) => TopTerm a -> PP.Doc
ppTopTerm (DataTerm dt _) = ppDataType dt
ppTopTerm (InterfaceTerm itf _) = ppInterface itf
ppTopTerm (SigTerm sig _) = text $ show sig
ppTopTerm (ClauseTerm cls _) = text $ show cls
ppTopTerm (DefTerm def _) = ppMultiHandlerDefinition def

ppDataType :: (Show a, HasSource a) => DataType a -> PP.Doc
ppDataType (MkDataType id tyVars ctrs a) = text "data" <+>
                              text id <+>
                              sep (map (text . show) tyVars) <+>
                              text "=" <+>
                              sep (map (text . show) ctrs)

ppInterface :: (Show a, HasSource a) => Interface a -> PP.Doc
ppInterface (MkInterface id tyVars cmds a) = text "interface" <+>
                           text id <+>
                           sep (map (text . show) tyVars) <+>
                           text "=" <+>
                           sep (map (text . show) cmds)

ppMultiHandlerDefinition :: (Show a, HasSource a) => MultiHandlerDefinition a -> PP.Doc
ppMultiHandlerDefinition (MkDef id cty cls _) =
  text id <+> text ":" <+> ppCompType cty
  $$ sep (map (ppClause id) cls)

ppClause :: (Show a, HasSource a) => Identifier -> Clause a -> PP.Doc
ppClause id (MkClause ps tm _) = text id <+>
                            (vcat . map ppPattern) ps <+> text "=" $$
                            (nest 3 . ppTerm) tm

ppPattern :: (Show a, HasSource a) => Pattern a -> PP.Doc
ppPattern (VPat vp _) = ppValuePat vp
ppPattern (CmdPat x n vps k _) = text "<" <+>
                                 text x <>
                                 (if n == 0 then empty
                                            else text "." <> int n) <+>
                                 (hcat . map ppValuePat) vps <+>
                                 text "->" <+>
                                 text k <+>
                                 text ">"
ppPattern (ThkPat x _) = text x

ppValuePat :: (Show a, HasSource a) => ValuePat a -> PP.Doc
ppValuePat (VarPat x _) = text x
ppValuePat (DataPat x vps _) = text x <+> (hcat . map ppValuePat) vps
ppValuePat (IntPat n _) = (text . show) n
ppValuePat (CharPat c _) = (text . show) c
ppValuePat (StrPat s _) = (text . show) s
ppValuePat (ConsPat vp1 vp2 _) = ppValuePat vp1 <+> text "::" <+> ppValuePat vp2
ppValuePat (ListPat vps _) = (hcat . map ppValuePat) vps

ppCompType :: (Show a, HasSource a) => CompType a -> PP.Doc
ppCompType (CompType ps q _) = text "{" <> ports <> peg <> text "}"
  where
    ports = case map ppPort ps of
      [] -> PP.empty
      xs -> foldl (\acc x -> x <+> text "-> " <> acc) PP.empty (reverse xs)
    peg = ppPeg q

ppValueType :: (Show a, HasSource a) => ValueType a -> PP.Doc
ppValueType (DTTy x ts _) = text x <+> foldl (<+>) PP.empty (map ppTypeArg ts)
ppValueType (SCTy cty _) = ppCompType cty
ppValueType (TVar x _) = text x
ppValueType (RTVar x _) = if isDebugVerboseOn () then text x else text $ trimVar x
ppValueType (FTVar x _) = if isDebugVerboseOn () then text x else text $ trimVar x
ppValueType (StringTy _) = text "String"
ppValueType (IntTy _) = text "Int"
ppValueType (CharTy _) = text "Char"

ppTypeArg :: (Show a, HasSource a) => TypeArg a -> PP.Doc
ppTypeArg (VArg t _) = ppParenValueType t
ppTypeArg (EArg ab _) = ppAb ab

{-# ANN ppParenValueType "HLint: ignore Use record patterns" #-}
ppParenValueType :: (Show a, HasSource a) => ValueType a -> PP.Doc
ppParenValueType v@(DTTy _ _ _) = text "(" <+> ppValueType v <+> text ")"
ppParenValueType v = ppValueType v

ppPort :: (Show a, HasSource a) => Port a -> PP.Doc
ppPort (Port []   ty _) = ppValueType ty
ppPort (Port adjs ty _) = text "<" <> PP.hsep (intersperse PP.comma $ map ppAdj adjs) <> text ">" <> ppValueType ty

ppPeg :: (Show a, HasSource a) => Peg a -> PP.Doc
ppPeg (Peg ab ty _) = ppAb ab <> ppValueType ty

ppAdj :: (Show a, HasSource a) => Adjustment a -> PP.Doc
ppAdj (ConsAdj x ts _) = ppInterfaceInstance (x, ts)
ppAdj (AdaptorAdj adp _) = ppAdaptor adp

ppAb :: (Show a, HasSource a) => Ability a -> PP.Doc
ppAb (MkAbility v (InterfaceMap m _) _) | M.null m = text "[" <> ppAbMod v <> text "]"
ppAb (MkAbility v m _) =
  text "[" <> ppAbMod v <+> text "|" <+> ppInterfaceMap m <> text "]"

ppAbMod :: (Show a, HasSource a) => AbilityMode a -> PP.Doc
ppAbMod (AbilityMode.Empty _) = text "0"
ppAbMod (AbilityMode.Var x _) = text x
ppAbMod (AbilityMode.RigidVar x _) = if isDebugVerboseOn () then text x else text $ trimVar x
ppAbMod (AbilityMode.FlexibleVar x _) = if isDebugVerboseOn () then text x else text $ trimVar x

ppInterfaceMap :: (Show a, HasSource a) => InterfaceMap a -> PP.Doc
ppInterfaceMap (InterfaceMap m _) =
  PP.hsep $ intersperse PP.comma $ map ppInterfaceInstances $ M.toList m

ppInterfaceInstances :: (Show a, HasSource a) => (Identifier, Bwd [TypeArg a]) -> PP.Doc
ppInterfaceInstances (x, instants) =
        PP.hsep
        $ intersperse PP.comma
        $ map (foldl (<+>) (text x) . map ppTypeArg) (bwd2fwd instants)

ppInterfaceInstance :: (Show a, HasSource a) => (Identifier, [TypeArg a]) -> PP.Doc
ppInterfaceInstance (x, ts) = text x <+> PP.hsep (map ppTypeArg ts)

ppSource :: Source -> PP.Doc
ppSource (InCode (line, col)) = text "line" <+> text (show line) <+> text ", column" <+> text (show col)
ppSource BuiltIn = text "built-in"
ppSource Implicit = text "implicit"
ppSource (ImplicitNear (line, col)) = text "implicit near line" <+> text (show line) <+> text ", column" <+> text (show col)
ppSource Generated = text "generated"


ppSourceOf :: (HasSource a) => a -> PP.Doc
ppSourceOf x = ppSource (getSource x)

ppTerm :: (Show a, HasSource a) => Term a -> PP.Doc
ppTerm (SC sc _) = ppSuspension sc
ppTerm (StrTerm str _) = text "{" <+> text str <+> text "}"
ppTerm (IntTerm n _) = text (show n)
ppTerm (CharTerm c _) = text (show c)
ppTerm (ListTerm xs _) = text "[" <+> sep (map ppTerm xs) <+> text "]"
ppTerm (TermSeq t1 t2 _) = PP.parens $ ppTerm t1 <+> text "; " <+> ppTerm t2
ppTerm (Use u _) = PP.parens $ ppUse u
ppTerm (DCon dc _) = PP.parens $ ppDataCon dc

ppSuspension :: (Show a, HasSource a) => Suspension a -> PP.Doc
ppSuspension (Suspension cls _) = text "{" <+> sep (map (ppClause "") cls) <+> text "}"

ppUse :: (Show a, HasSource a) => Use a -> PP.Doc
ppUse (RawIdentifier x _) = text x
ppUse (RawComb u args _) = PP.lparen <> ppUse u <+> ppArgs args <> PP.rparen
ppUse (Op op _) = ppOperator op
ppUse (App u args _) = PP.lparen <> ppUse u <+> ppArgs args <> PP.rparen
ppUse (Adapted rs t _) =
  PP.parens $ text "<" <> ppAdaptors rs <> text ">" <+> ppUse t

-- TODO: LC: fix parenthesis output...
ppArgs :: (Show a, HasSource a) => [Term a] -> PP.Doc
ppArgs [] = text "!"
ppArgs args = sep (map ppTerm args)

ppOperator :: (Show a, HasSource a) => Operator a -> PP.Doc
ppOperator (Mono x _) = text x
ppOperator (Poly x _) = text x
ppOperator (CmdIdentifier x _) = text x

ppDataCon :: (Show a, HasSource a) => DataCon a -> PP.Doc
ppDataCon (DataCon x tms _) = text x <+> sep (map ppTerm tms)

ppAdaptors :: (Show a, HasSource a) => [Adaptor a] -> PP.Doc
ppAdaptors rs = PP.hsep $ intersperse PP.comma $ map ppAdaptor rs

ppAdaptor :: (Show a, HasSource a) => Adaptor a -> PP.Doc
ppAdaptor (Adaptor.Raw x liat left right _) =
  text x <> text "(" <> text (show liat) <+> sep (punctuate (text " ") (map (text . show) left)) <+> text "->" <+> sep (punctuate (text " ") (map (text . show) right)) <> text ")"
ppAdaptor (Adaptor.Adp x mm ns _) =
  text x <> text "(" <> text (show mm) <> comma <+> sep (punctuate comma (map int ns)) <> text ")"
ppAdaptor (Adaptor.Compilable x m ns _) =
  text x <> text "(" <> sep (punctuate comma (map int ns)) <> text ")(" <>
  int m <> text ")"

{- TypeCheckCommon pretty printers -}

ppContext :: Context -> PP.Doc
ppContext = ppFwd . map ppEntry . bwd2fwd

ppEntry :: Entry -> PP.Doc
ppEntry (FlexMVar x decl) = text "FlexMVar " <+> text x <+> text "\t=\t\t" <+> ppDecl decl
ppEntry (TermVar op ty)   = text "TermVar " <+> text (show op) <+> text "\t:=\t" <+> ppValueType ty
ppEntry Mark              = text "<Mark>"

ppDecl :: Decl -> PP.Doc
ppDecl Hole        = text "?"
ppDecl (TyDefn ty) = text "val.ty. " <+> ppValueType ty
ppDecl (AbDefn ab) = text "eff.ty. " <+> ppAb ab

ppSuffix :: Suffix -> PP.Doc
ppSuffix = ppFwd . map (\(x, d) -> "(" ++ show x ++ "," ++ show (ppDecl d) ++ ")")

ppInterfaces :: [Identifier] -> PP.Doc
ppInterfaces p = PP.hsep $ intersperse PP.comma $ map text p

{- BWDFWD pretty printers -}

ppFwd :: Show a => [a] -> PP.Doc
ppFwd [] = text "[]"
ppFwd xs = text "[" $$
           sep (map (nest 3 . text . show) xs) $$
           text "]"

ppBwd :: Show a => Bwd a -> PP.Doc
ppBwd = ppFwd . bwd2fwd

{- Shonky pretty printers -}

-- Pretty printing routines

ppProgShonky :: [Def Exp] -> PP.Doc
ppProgShonky xs = vcat (punctuate (text "\n") (map ppDef xs))

ppDef :: Def Exp -> PP.Doc
ppDef (id := e) = text id <+> text "->" <+> ppExp e
ppDef (DF id [] []) = error "ppDef invariant broken: empty Def Exp detected."
ppDef p@(DF id hss es) = header $+$ vcat cs
  where header = text id <> PP.parens (hsep portAnnots) <> colon
        portAnnots = punctuate comma $ map ppPort hss
        cs = punctuate comma $
               map (\x -> text id <> nest 3 (ppClauseShonky ($$) x)) es
        ppPort :: ([Adap], [String]) -> PP.Doc
        ppPort (adps, cmds) = PP.parens (hsep (punctuate comma (map ppAdap adps))
                            <+> comma <+> hsep (punctuate comma (map text cmds)))
        ppAdap :: Adap -> PP.Doc
        ppAdap (cmds, r) = text "([" <> hsep (punctuate comma (map text cmds)) <> text "]" <+>
                           comma <+> ppRenaming r <+> text ")"
-- TODO: LC: refactor above pretty-printer

ppText :: (a -> PP.Doc) -> [Either Char a] -> PP.Doc
ppText f (Left c : xs) = text (escChar c) <> ppText f xs
ppText f (Right x : xs) = text "`" <> f x <> text "`" <> ppText f xs
ppText f [] = text "|]"

isEscChar :: Char -> Bool
isEscChar c = c `elem` ['\n','\t','\b']

escChar :: Char -> String
escChar c = f [('\n', "\\n"),('\t', "\\t"),('\b', "\\b")]
  where f ((c',s):xs) = if c == c' then s else f xs
        f [] = [c]

ppClauseShonky :: (PP.Doc -> PP.Doc -> PP.Doc) -> ([Pat], Exp) -> PP.Doc
ppClauseShonky comb (ps, e) =
  let rhs = PP.parens (hsep $ punctuate comma (map ppPat ps))
      lhs = ppExp e in
  rhs <+> text "->" `comb` lhs

ppExp :: Exp -> PP.Doc
ppExp (EV x) = text x
ppExp (EI n) = int n
ppExp (EA x) = text $ "'" ++ x
ppExp (e :& e') | isListExp e = text "[" <> ppListExp e'
ppExp p@(_ :& _) = text "[" <> ppExp' p
ppExp (f :$ xs) = let args = hcat $ punctuate comma (map ppExp xs) in
  ppExp f <> text "(" <> args <> text ")"
ppExp (e :! e') = ppExp e <> semi <> ppExp e'
ppExp (e :// e') = ppExp e <> text "/" <> ppExp e'
ppExp (EF xs ys) =
-- TODO: LC: Print xs
  let clauses = map (ppClauseShonky (<+>)) ys in
  PP.braces $ hcat (punctuate comma clauses)
ppExp (EX xs) = text "[|" <> ppText ppExp xs
ppExp (ER (cs, r) e) = text "<(" <+> hcat (punctuate comma (map text cs))
                    <> text ")" <+> ppRenaming r <> text ">"
                    <+> PP.parens (ppExp e)

ppExp' :: Exp -> PP.Doc
ppExp' (e :& EA "") = ppExp e <> rbrack
ppExp' (e :& es) = ppExp e <> comma <> ppExp' es
ppExp' e = ppExp e

isListExp :: Exp -> Bool
isListExp (e :& _) = isListExp e
isListExp _ = False

-- Special case for lists
ppListExp :: Exp -> PP.Doc
ppListExp (e :& EA "") = ppExp e <> text "]"
ppListExp (e :& es) = ppExp e <> text "|" <> ppListExp es
ppListExp (EA "") = text "]"
ppListExp _ = text "ppListExp: invariant broken"

ppPat :: Pat -> PP.Doc
ppPat (PV x) = ppVPat x
ppPat (PT x) = PP.braces $ text x
ppPat (PC cmd n ps k) = let args = hcat $ punctuate comma (map ppVPat ps) in
  let cmdtxt = text (cmd ++ ".") <> int n in
  PP.braces $ text "'" <> cmdtxt <> PP.parens args <+> text "->" <+> text k

ppVPat :: VPat -> PP.Doc
ppVPat (VPV x) = text x
ppVPat (VPI n) = int n
ppVPat (VPA x) = text $ "'" ++ x
ppVPat (VPX xs) = text "[|" <> ppText ppVPat xs
ppVPat (v1 :&: v2 :&: v3) = ppVPat (v1 :&: (v2 :&: v3))
ppVPat (v :&: v') | isListPat v = lbrack <> ppVPatList v'
ppVPat p@(_ :&: _) = lbrack <> ppVPat' p

ppVPatList :: VPat -> PP.Doc
ppVPatList (v :&: VPA "") = ppVPat v <> rbrack
ppVPatList (v :&: vs) = ppVPat v <> text "|" <> ppVPatList vs
ppVPatList (VPA "") = lbrack
ppVPatList _ = error "ppVPatList: broken invariant"

ppVPat' :: VPat -> PP.Doc
ppVPat' (v :&: VPA "") = ppVPat v <> text "]"
ppVPat' (v :&: vs) = ppVPat v <> comma <> ppVPat' vs
ppVPat' v = ppVPat v

isListPat :: VPat -> Bool
isListPat (v :&: _) = isListPat v
isListPat _ = False
