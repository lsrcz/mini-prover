module MiniProver.TopLevel.TopLoop where

import Text.Megaparsec
import MiniProver.Parser.Parser
import MiniProver.Core.Syntax
import MiniProver.Core.Context
import MiniProver.Core.Build
import MiniProver.Core.IndPos
import MiniProver.Core.Termination
import MiniProver.Core.Typing
import MiniProver.Core.NameBounding
import MiniProver.PrettyPrint.PrettyPrint
import MiniProver.PrettyPrint.PrettyPrintAST
import MiniProver.PrettyPrint.Colorful
import MiniProver.TopLevel.Command
import Data.List (elemIndex)
import Data.Either (fromRight)
import Control.Monad (forever,when)
import System.IO

-- printing functions for verbose levels
printIfNoLessThan :: (Show a) => Int -> Int -> a -> IO ()
printIfNoLessThan i threshold x =
  when (i >= threshold) $ print x

putStrIfNoLessThan :: Int -> Int -> String -> IO ()
putStrIfNoLessThan i threshold str =
  when (i >= threshold) $ putStr str

putStrLnIfNoLessThan :: Int -> Int -> String -> IO ()
putStrLnIfNoLessThan i threshold str =
  when (i >= threshold) $ putStrLn str

prettyPrintIfNoLessThan :: Int -> Int -> Term -> IO ()
prettyPrintIfNoLessThan i threshold tm =
  when (i >= threshold) $ prettyPrint tm

prettyPrintCommandIfNoLessThan :: Int -> Int -> Command -> IO ()
prettyPrintCommandIfNoLessThan i threshold cmd =
  when (i >= threshold) $ prettyPrintCommand cmd

prettyPrintASTIfNoLessThan :: Int -> Int -> Term -> IO ()
prettyPrintASTIfNoLessThan i threshold tm =
  when (i >= threshold) $ prettyPrintAST tm

prettyPrintCommandASTIfNoLessThan :: Int -> Int -> Command -> IO ()
prettyPrintCommandASTIfNoLessThan i threshold cmd =
  when (i >= threshold) $ prettyPrintCommandAST cmd

getInputCommand :: IO String
getInputCommand = do
  str <- getLine 
  case elemIndex '.' str of
    Just t -> return $ take (t + 1) str
    Nothing -> do
      str1 <- getInputCommand
      return $ str ++ " " ++ str1

isIndCommand :: Command -> Bool
isIndCommand cmd =
  case cmd of
    Ind{} -> True
    _ -> False

errorColor :: String -> String
errorColor = frontGroundColor BRED

infoColor :: String -> String
infoColor = frontGroundColor BYELLOW

okColor :: String -> String
okColor = frontGroundColor BGREEN

topLoop :: Int -> Context -> IO Context
topLoop verboseLevel ctx = forever $ do
  let
    putStrLnV = putStrLnIfNoLessThan verboseLevel
  inputStr <- getInputCommand
  putStrLnV 1 $ okColor "[ OK ] reading in"
  putStrLnV 2 $ infoColor "**** input string ****"
  putStrLnV 2 inputStr
  newCtx <- processOneCommand verboseLevel inputStr ctx
  topLoop verboseLevel newCtx

removeLeadingSpaces :: String -> String
removeLeadingSpaces [] = []
removeLeadingSpaces str@(x:xs)
  | x == ' ' = removeLeadingSpaces xs
  | otherwise = str

showOrdinal :: Int -> String
showOrdinal i
  | i == 1 = "1st"
  | i == 2 = "2nd"
  | otherwise = show i ++ "st"

hGetInputCommand :: Handle -> IO String
hGetInputCommand handle = do
  eofFlag <- hIsEOF handle
  if eofFlag
    then return ""
    else do
      str <- hGetLine handle
      case elemIndex '.' str of
        Just t -> return $ take (t + 1) str
        Nothing -> do
          str1 <- hGetInputCommand handle
          return $ str ++ " " ++ str1

processFile :: Handle -> Int -> Context -> IO Context
processFile handle verboseLevel ctx = do
  eofFlag <- hIsEOF handle
  if eofFlag
    then return ctx
    else do
      let
        putStrLnV = putStrLnIfNoLessThan verboseLevel
      inputStr <- hGetInputCommand handle
      let
        inputStrNoSpace = removeLeadingSpaces inputStr
      putStrLnV 1 $ okColor "[ OK ] reading in"
      putStrLnV 2 $ infoColor "**** input string ****"
      putStrLnV 2 inputStrNoSpace
      newCtx <- processOneCommand verboseLevel inputStrNoSpace ctx
      processFile handle verboseLevel newCtx

processOneCommand :: Int -> String -> Context -> IO Context
processOneCommand verboseLevel inputStr ctx = do
  -- verbose printting functions
  let
    printV :: (Show a) => Int -> a -> IO ()
    printV = printIfNoLessThan verboseLevel
    putStrV = putStrIfNoLessThan verboseLevel
    putStrLnV = putStrLnIfNoLessThan verboseLevel
    pPrintV = prettyPrintIfNoLessThan verboseLevel
    pPrintCmdV = prettyPrintCommandIfNoLessThan verboseLevel
    pPrintASTV = prettyPrintASTIfNoLessThan verboseLevel
    pPrintCmdASTV = prettyPrintCommandASTIfNoLessThan verboseLevel

  -- parsing
  let rawcmd = parse pcommand "" inputStr
  case rawcmd of
    Left err -> do
      putStrLn $ errorColor "[ FAIL ] parsing"
      print err
      return ctx
    Right cmd -> do
      putStrLnV 1 $ okColor "[ OK ] parsing"
      putStrLnV 2 $ infoColor "**** parsing result (term) ****"
      pPrintCmdV 2 cmd
      putStrLnV 3 $ infoColor "**** parsing result (AST) ****"
      pPrintCmdASTV 3 cmd

      case checkDuplicateGlobalName ctx cmd of
        lst@(_:_) -> do
          putStrLn $ errorColor "[ FAIL ] duplicate name checking"
          putStrLn $ "Name " ++ unwords lst ++ " exists"
          return ctx
        [] -> do
          putStrLn $ okColor "[ OK ] duplicate name checking"
          case checkAllNameBoundedCommand ctx cmd of
            AllNameBounded -> do
              putStrLnV 1 $ okColor "[ OK ] name checking"
              case buildCommand cmd ctx of
                Ind{}
                  | not $ isPositive ctx cmd -> do
                    putStrLnV 1 $ okColor "[ OK ] nameless representation building"
                    putStrLn $ errorColor "[ FAIL ] positivity checking"
                    return ctx
                boundedCmd -> do
                  putStrLnV 1 $ okColor "[ OK ] nameless representation building"
                  when (isIndCommand boundedCmd) $
                    putStrLnV 1 $ okColor "[ OK ] positivity checking"
                  putStrLnV 2 $ infoColor "**** building result (command) ****"
                  pPrintCmdV 2 boundedCmd
                  putStrLnV 3 $ infoColor "**** building result (AST) ****"
                  pPrintCmdASTV 3 boundedCmd
                  return ctx
                
                  case computeDecParamCmd boundedCmd of
                    Left tm -> do
                      putStrLn $ errorColor "[ FAIL ] termination checking"
                      putStrLn "This term may not be terminating"
                      prettyPrint tm
                      return ctx
                    Right cmdWithDec -> do
                      putStrLnV 1 $ okColor "[ OK ] termination checking"
                      putStrLnV 2 $ infoColor "**** command with dec annotation ****"
                      pPrintCmdV 2 cmdWithDec
                      putStrLnV 3 $ infoColor "**** command with dec annotation (AST) ****"
                      pPrintCmdASTV 3 cmdWithDec

                      case checkCommandType ctx cmdWithDec of
                        Just (TypingError tm err) -> do
                          putStrLn $ errorColor "[ FAIL ] type checking"
                          putStrLn "In term:\n"
                          prettyPrint tm
                          putStrLn err
                          return ctx
                        Nothing -> do
                          putStrLnV 1 $ okColor "[ OK ] type checking"
                          let newctx = addEnvCommand ctx cmdWithDec
                          if length newctx == length ctx
                            then do
                              putStrLn $ errorColor "[ FAIL ] adding to context"
                              putStrLn "Some features are not implemented"
                              return ctx
                            else do
                              putStrLnV 1 $ okColor "[ OK ] adding to context"
                              case cmdWithDec of
                                Ax name _ -> do
                                  putStrLnV 2 $ infoColor "**** type declared ****"
                                  pPrintV 2 $ fromRight (error "this should not happen") $ getBindingType newctx 0
                                  putStrLn $ name ++ " is declared"
                                Def name _ _ -> do
                                  putStrLnV 2 $ infoColor "**** term defined ****"
                                  pPrintV 2 $ fromRight (error "this should not happen") $ getBindingTerm newctx 0
                                  putStrLnV 2 $ infoColor "**** type defined ****"
                                  pPrintV 2 $ fromRight (error "this should not happen") $ getBindingType newctx 0
                                  putStrLn $ name ++ " is defined"
                                Fix name (TmFix i _) -> do
                                  putStrLnV 2 $ infoColor "**** term defined ****"
                                  pPrintV 2 $ fromRight (error "this should not happen") $ getBindingTerm newctx 0
                                  putStrLnV 2 $ infoColor "**** type defined ****"
                                  pPrintV 2 $ fromRight (error "this should not happen") $ getBindingType newctx 0
                                  putStrLn $ name ++ " is defined"
                                  putStrLn $ name ++ " is recursively defined (decreasing on " ++
                                    showOrdinal i ++ " argument)"
                                Ind name _ _ _ _ -> do
                                  putStrLnV 2 $ infoColor "**** inductive principle term defined ****"
                                  pPrintV 2 $ fromRight (error "this should not happen") $ getBindingTerm newctx 0
                                  putStrLnV 2 $ infoColor "**** inductive principle type defined ****"
                                  pPrintV 2 $ fromRight (error "this should not happen") $ getBindingType newctx 0
                                  putStrLn $ name ++ " is defined"
                                  putStrLn $ name ++ "_rect is defined"
                              return newctx
                          
                    
            err -> do
              putStrLn $ errorColor "[ FAIL ] name checking"
              print err
              return ctx
