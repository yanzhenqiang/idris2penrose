module Precisely where

import Base
import Ast
import Parser
import Typer
import Kiselyov
import RTS

data Mode = Check | Compile | Raw | Run | Wasm deriving (Eq, Show)

parseMode "check"   = Just Check
parseMode "compile" = Just Compile
parseMode "raw"     = Just Raw
parseMode "run"     = Just Run
parseMode "wasm"    = Just Wasm
parseMode _         = Nothing

main :: IO ()
main = do
  args <- getArgs
  case args of
    [] -> putStrLn "Usage: precisely <check|compile|raw|run|wasm> <file.x>"
    (modeStr:rest) -> case parseMode modeStr of
      Nothing -> putStrLn $ "Unknown mode: " ++ modeStr
      Just mode -> case rest of
        [] -> putStrLn "No input file specified."
        (f:_) -> do
          src <- readFile f
          case parseFile src of
            Left err -> putStrLn $ "Parse error: " ++ err
            Right prog -> do
              putStrLn $ "Parsed " ++ show (length prog) ++ " declarations."
              case typecheck prog of
                Left err -> putStrLn $ "Type error: " ++ err
                Right (ctx, _) -> do
                  putStrLn "Type checking OK."
                  case mode of
                    Check -> pure ()
                    Compile -> putStr $ outputC $ compileProgram prog
                    Raw -> putStr $ outputRaw $ compileProgram prog
                    Run -> do
                      putStr $ outputC $ compileProgram prog
                      putStrLn "-- Run: pipe output to a C compiler"
                    Wasm -> do
                      putStr $ outputWasmC $ compileProgram prog
                      putStrLn "-- WebAssembly C-for-WASM output above"

-- FFI helpers
foreign import ccall "putchar" putChar :: Int -> IO Int
foreign import ccall "getchar" getChar :: IO Int
foreign import ccall "getargcount" getArgCount :: IO Int
foreign import ccall "getargchar" getArgChar :: Int -> Int -> IO Char

putStrLn :: String -> IO ()
putStrLn s = mapM_ (putChar . ord) s >> putChar (ord '\n') >> pure ()

getArgs :: IO [String]
getArgs = do
  n <- getArgCount
  mapM (\i -> do
    let go k = do
          c <- getArgChar i k
          if c == '\0' then pure [] else (c:) <$> go (k+1)
    go 0) [0..n-1]

readFile :: String -> IO String
readFile path = interact id

interact :: (String -> String) -> IO String
interact f = do
  s <- getContents
  pure (f s)

getContents :: IO String
getContents = do
  c <- getChar
  if c == (-1) then pure [] else (chr c :) <$> getContents

-- Debug: show parsed program.
showProgram :: Program -> String
showProgram = unlines . map showDecl
  where
    showDecl (TypeSig n ty) = n ++ " : " ++ ppTerm ty
    showDecl (FunDef n cs) = n ++ " = " ++ intercalate " | " (map (\(Clause ps rhs) -> unwords (map ppPat ps) ++ " => " ++ ppTerm rhs) cs)
    showDecl (DataDecl d cs) = "data " ++ d ++ " = " ++ intercalate " | " (map (\(c, ts) -> c ++ " " ++ unwords (map ppTerm ts)) cs)
    showDecl (InfixDecl f prec ops) = show f ++ " " ++ show prec ++ " " ++ unwords ops
