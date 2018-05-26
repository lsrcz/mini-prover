module MiniProver.TopLevel.TopLoop where

import Text.Megaparsec
import Control.Monad (when)
import MiniProver.Core.Syntax
import MiniProver.Parser.Parser
import MiniProver.Core.Context
import MiniProver.Core.Build
--import MiniProver.Core.IndPos
--import MiniProver.Core.Termination
--import MiniProver.Core.Typing
import MiniProver.PrettyPrint.PrettyPrint
import MiniProver.PrettyPrint.PrettyPrintAST
import MiniProver.PrettyPrint.Colorful
import MiniProver.Core.NameBounding
import Data.List (elemIndex)

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

processOneCommand :: Int -> Context -> IO Context
processOneCommand verboseLevel ctx = do
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
    errorColor = frontGroundColor BRED
    infoColor = frontGroundColor BYELLOW
    okColor = frontGroundColor BGREEN
      

  -- reading inpus
  inputStr <- getInputCommand
  putStrLnV 1 $ okColor "[ OK ] reading in"
  putStrLnV 2 $ infoColor "**** input string ****"
  putStrLnV 2 inputStr

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
      putStrLnV 3 $ infoColor"**** parsing result (AST) ****"
      pPrintCmdASTV 3 cmd

      case checkAllNameBoundedCommand ctx cmd of
        AllNameBounded -> do
          putStrLnV 1 $ okColor "[ OK ] name checking"
          case buildCommand cmd ctx of
            {-Ind{}
              | not $ isPositive ctx cmd -> do
                putStrLnV 1 $ okColor "[ OK ] nameless representation building"
                putStrLn $ errorColor "[ FAIL ] positivity checking"
                return ctx-}
            boundedCmd -> do
              putStrLnV 1 $ okColor "[ OK ] nameless representation building"
              when (isIndCommand boundedCmd) $
                putStrLnV 1 $ okColor "[ OK ] positivity checking"
              putStrLnV 2 $ infoColor "**** building result (command) ****"
              pPrintCmdV 2 boundedCmd
              putStrLnV 3 $ infoColor "**** building result (AST) ****"
              pPrintCmdASTV 3 boundedCmd
              return ctx
{-
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
                  return ctx
                -}
        err -> do
          putStrLn $ errorColor "[ FAIL ] name checking"
          print err
          return ctx
