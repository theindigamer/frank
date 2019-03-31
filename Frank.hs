{-# LANGUAGE GADTs #-}
module Main where

import Parser
import Compile
import TypeCheck
import Syntax
import Syntax.Refine
import Syntax.Desugar
import Debug

import qualified Shonky.Semantics as Shonky

import Control.Monad

import Data.IORef
import qualified Data.Map.Strict as M
import Data.List
import Data.Maybe (fromMaybe)

import System.Console.CmdArgs.Explicit
import System.Directory
import System.Environment
import System.Exit
import System.IO

type Args = [(String, [String])]

type PMap = M.Map FilePath (Program Raw)

-- Function checks whether or not a main function exists in the program
existsMain :: Program t -> Bool
existsMain (MkProgram xs) = "main" `elem` [ident | DefTerm (MkDef ident _ _ _) _ <- xs]

splice :: Program Raw -> Term Raw -> Program Raw
splice (MkProgram xs) tm = MkProgram $ xs ++ ys
  where
    ys = [sig, cls]
    sig = SigTerm (MkSig ident (CompType [] peg b) b) b
    peg = Peg ab ty b
    ty = TVar "%X" b
    ab = Ab (AbVar "£" b) (InterfaceMap M.empty (Raw Generated)) b
    cls = ClauseTerm (MkMHClause ident (MkClause [] tm b) b) b
    ident = "%eval"
    b = Raw Generated

--TODO: LC: Fix locations?
exorcise :: Program Desugared -> (Program Desugared, TopTerm Desugared)
exorcise (MkProgram xs) = (prog, DefTerm (head evalDef) a)
  where prog = MkProgram (map (swap DataTerm a) dts ++
                       map (swap InterfaceTerm a) itfs ++
                       map (swap DefTerm a) hdrs)
        dts = [d | DataTerm d _ <- xs]
        itfs = [i | InterfaceTerm i _ <- xs]
        defs = [d | DefTerm d _ <- xs]
        (evalDef,hdrs) = partition isEvalTerm defs
        isEvalTerm (MkDef id _ _ _) = id == "%eval"
        a = Desugared Generated

extractEvalUse :: TopTerm Desugared -> Use Desugared
extractEvalUse (DefTerm (MkDef _ _ [cls] _) _) = getBody cls
  where getBody (MkClause [] (Use u _) _) = u
        getBody _ = error "extractEvalUse: eval body invariant broken"

glue :: Program Desugared -> TopTerm Desugared -> Program Desugared
glue (MkProgram xs) x = MkProgram (x : xs)

parseProgram :: FilePath -> Args -> IO (Either String (Program Raw))
parseProgram fileName args =
  do m <- pProgram (Right M.empty) fileName
     case m of
       Left msg  -> return $ Left msg
       Right map -> return $ Right $ MkProgram $ M.foldl combine [] map
  where pProgram :: Either String PMap -> FilePath -> IO (Either String PMap)
        pProgram (Left msg) _ = return $ Left msg
        pProgram (Right map) fname | M.member fname map = return $ Right map
        pProgram (Right map) fname =
          let ext = if ".fk" `isSuffixOf` fname then "" else ".fk" in
          do m <- parseFile (fname ++ ext) incPaths
             case m of
               Left msg -> return $ Left msg
               Right (p,fs) -> foldM pProgram (Right (M.insert fname p map)) fs

        combine :: [TopTerm Raw] -> Program Raw -> [TopTerm Raw]
        combine xs (MkProgram ys) = xs ++ ys

        incPaths :: [String]
        incPaths = fromMaybe [] (lookup "inc" args)

        parseFile :: String -> [FilePath] ->
                     IO (Either String (Program Raw,[String]))
        parseFile name incs = let fs = name : map (++ name) incs in
          do m <- foldM g Nothing fs
             case m of
               Nothing ->
                 die ("could not find " ++ name ++
                      " in search path:" ++ intercalate "," fs)
               Just x -> runTokenProgParse <$> readFile x
          where g :: Maybe FilePath -> FilePath -> IO (Maybe FilePath)
                g Nothing x = do b <- doesFileExist x
                                 return $ if b then Just x else Nothing
                g x@(Just _) _ = return x

parseEvalTerm :: String -> IO (Term Raw)
parseEvalTerm v = case runTokenParse tm v of
  Left err -> die err
  Right tm -> return tm

refineComb :: Either String (Program Raw) -> Term Raw -> IO (Program Refined)
refineComb prog tm = case prog of
    Left err -> die err
    Right p -> case refine (splice p tm) of
      Left err -> die err
      Right p' -> return p'

refineAndDesugarProgram :: Either String (Program Raw) -> IO (Program Desugared)
refineAndDesugarProgram p =
  case p of
    Left err -> die err
    Right p -> case refine p of
      Left err -> die err
      Right p' -> return $ desugar p'

checkProgram :: Program Desugared -> Args -> IO (Program Desugared)
checkProgram p _ =
  case check p of
    Left err -> die err
    Right p' -> return p'

checkUse :: Program Desugared -> Use Desugared -> IO (Use Desugared, ValueType Desugared)
checkUse p use =
  case inferEvalUse p use of
    Left err -> die err
    Right (use, ty) -> return (use, ty)

compileProgram :: String -> Program Desugared -> Args -> IO Shonky.Env
compileProgram progName p args =
  if ("output-shonky",[]) `elem` args then
    do compileToFile p progName
       Shonky.loadFile progName
  else return $ Shonky.load $ compile p

evalProgram :: Shonky.Env -> String -> IO ()
evalProgram env tm =
  case Shonky.try env tm of
    Shonky.Ret v -> print (Shonky.ppVal v)
    comp -> do -- putStrLn $ "Generated computation: " ++ show comp
               v <- Shonky.ioHandler comp
               print (Shonky.ppVal v)

compileAndRunProgram :: String -> Args -> IO ()
compileAndRunProgram fileName args =
  do let progName = takeWhile (/= '.') fileName
     prog <- parseProgram fileName args
     case lookup "eval" args of
       Just [v] -> do tm <- parseEvalTerm v
                      -- lift tm to top term and append to prog
                      p <- refineComb prog tm
                      -- tear apart again
                      let (p',ttm) = exorcise (desugar p)
                          use = extractEvalUse ttm
                      p'' <- checkProgram p' args
                      (use', _) <- checkUse p'' use
                      env <- compileProgram progName (glue p'' ttm) args
                      evalProgram env "%eval()"
       Just _ -> die "only one evaluation point permitted"
       Nothing -> do p <- refineAndDesugarProgram prog
                     p' <- checkProgram p args
                     env <- compileProgram progName p' args
                     case lookup "entry-point" args of
                       Just [v] -> evalProgram env (v ++ "()")
                       Just _  -> die "only one entry point permitted"
                       Nothing ->
                         if existsMain p' then
                           evalProgram env "main()"
                         else
                           putStrLn ("Compilation successful! " ++
                                     "(no main function defined)")
arguments :: Mode Args
arguments =
  mode "frank" [] "Frank program" (flagArg (upd "file") "FILE")
  [flagNone ["output-shonky"] (("output-shonky",[]):)
   "Output Shonky code"
  ,flagNone ["debug-output"] (("debug-output",[]):)
   "Enable all debugging facilities"
  ,flagNone ["debug-verbose"] (("debug-verbose",[]):)
   "Enable verbose variable names etc. on output"
  ,flagNone ["debug-parser"] (("debug-parser",[]):)
    "Enable output of parser logs"
  ,flagNone ["debug-tc"] (("debug-tc",[]):)
   "Enable output of type-checking logs"
  ,flagReq ["include", "I"] updInc "INC"
   "Add a search path for source files"
  ,flagReq ["eval"] (upd "eval") "USE"
   "Run Frank computation USE (default: main!)"
  ,flagReq ["entry-point"] (upd "entry-point") "NAME"
   "Run computation NAME (default: main)"
  ,flagHelpSimple (("help",[]):)]
  where upd msg x v = Right $ (msg,[x]):v
        updInc x args = case lookup "inc" args of
          Just xs -> Right $ ("inc",x:xs):args
          Nothing -> Right $ ("inc",[x]):args

-- handy for testing in ghci
run f = compileAndRunProgram f []

main :: IO ()
main = do
  hSetBuffering stdin NoBuffering
  hSetEcho stdin False
  args <- processArgs arguments
  let debugVerboseOn =   ("debug-output",[]) `elem` args ||
                         ("debug-verbose", []) `elem` args
      debugParserOn =    ("debug-output",[]) `elem` args ||
                         ("debug-parser", []) `elem` args
      debugTypeCheckOn = ("debug-output",[]) `elem` args ||
                         ("debug-tc", []) `elem` args
  writeIORef debugMode (debugVerboseOn, debugParserOn, debugTypeCheckOn)
  if ("help",[]) `elem` args then
     print $ helpText [] HelpFormatDefault arguments
  else case lookup "file" args of
    Just [f] -> compileAndRunProgram f args
    Just _  -> die "too many Frank sources specified."
    Nothing -> die "no Frank source specified."
