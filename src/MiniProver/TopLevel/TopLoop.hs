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
import MiniProver.Core.SimplifyIndType
import MiniProver.PrettyPrint.PrettyPrint
import MiniProver.PrettyPrint.PrettyPrintAST
import MiniProver.PrettyPrint.Colorful
import MiniProver.TopLevel.Command
import MiniProver.TopLevel.IO
import MiniProver.TopLevel.ProofLoop
import MiniProver.PrettyPrint.PrintingCommand
import Data.Either (fromRight)
import Control.Monad (forever,when)
import System.IO

isIndCommand :: Command -> Bool
isIndCommand cmd =
  case cmd of
    Ind{} -> True
    _ -> False

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

showOrdinal :: Int -> String
showOrdinal i
  | i == 1 = "1st"
  | i == 2 = "2nd"
  | otherwise = show i ++ "st"

processFile :: Handle -> Int -> Context -> IO Context
processFile handle verboseLevel ctx = do
  eofFlag <- hIsEOF handle
  if eofFlag
    then return ctx
    else do
      let
        putStrLnV = putStrLnIfNoLessThan verboseLevel
      inputStr <- hGetInputCommand handle
      putStrLnV 1 $ okColor "[ OK ] reading in"
      putStrLnV 2 $ infoColor "**** input string ****"
      putStrLnV 2 inputStr
      newCtx <- processOneCommand verboseLevel inputStr ctx
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

    pPrintTopTy ctx = pPrintV 2 $ fromRight (error "this should not happen") $ getBindingType ctx 0
    pPrintTopTm ctx = pPrintV 2 $ fromRight (error "this should not happen") $ getBindingTerm ctx 0
    pPrintTopTyAST ctx = pPrintASTV 3 $ fromRight (error "this should not happen") $ getBindingType ctx 0
    pPrintTopTmAST ctx = pPrintASTV 3 $ fromRight (error "this should not happen") $ getBindingTerm ctx 0

  -- parsing
  let rawcmd = parse pcommand "" inputStr
  case rawcmd of
    Left err -> do
      putStrLn $ errorColor "[ FAIL ] parsing"
      print err
      return ctx
    Right (Print nm) -> do
      processPrint ctx nm
      return ctx
    Right (PrintAST nm) -> do
      processPrintAST ctx nm
      return ctx
    Right cmd -> do
      putStrLnV 1 $ okColor "[ OK ] parsing"
      case cmd of
        Check _ -> return ()
        _ -> do
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
                  case cmd of
                    Check _ -> return ()
                    _ -> do
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
                    Right (Check tm) -> do
                      putStrLnV 1 $ okColor "[ OK ] termination checking"
                      case typeof ctx tm of
                        Left (TypingError tm1 err) -> do
                          putStrLn "In term:\n"
                          prettyPrint tm1
                          putStrLn err
                        Right ty -> do
                          prettyPrint (simplifyIndType tm)
                          putStrLn $ "     : " ++ drop 7 (addIndent 7 $ prettyShow ty)
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
                          case cmdWithDec of
                            Theorem name ty -> do
                              result <- proof ctx (simplifyIndType ty)
                              case result of
                                Left AdmittedCmd -> do
                                  putStrLn $ name ++ " is declared"
                                  return $ addBinding ctx name $
                                    TmAbbBind (simplifyIndType ty) Nothing
                                Left AbortCmd -> do
                                  putStrLn "Aborted"
                                  return ctx
                                Right tm -> do
                                  putStrLn $ name ++ " is defined"
                                  return $ addBinding ctx name $
                                    TmAbbBind (simplifyIndType ty) $ Just tm
                            _ -> do
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
                                      pPrintTopTy newctx
                                      putStrLnV 3 $ infoColor "**** type declared (AST) ****"
                                      pPrintTopTyAST newctx
                                      putStrLn $ name ++ " is declared"
                                    Def name _ _ -> do
                                      putStrLnV 2 $ infoColor "**** term defined ****"
                                      pPrintTopTm newctx
                                      putStrLnV 3 $ infoColor "**** term defined (AST) ****"
                                      pPrintTopTmAST newctx
                                      putStrLnV 2 $ infoColor "**** type defined ****"
                                      pPrintTopTy newctx
                                      putStrLnV 3 $ infoColor "**** type defined (AST) ****"
                                      pPrintTopTyAST newctx
                                      putStrLn $ name ++ " is defined"
                                    Fix name (TmFix i _) -> do
                                      putStrLnV 2 $ infoColor "**** term defined ****"
                                      pPrintTopTm newctx
                                      putStrLnV 3 $ infoColor "**** term defined (AST) ****"
                                      pPrintTopTmAST newctx
                                      putStrLnV 2 $ infoColor "**** type defined ****"
                                      pPrintTopTy newctx
                                      putStrLnV 3 $ infoColor "**** type defined (AST) ****"
                                      pPrintTopTyAST newctx
                                      putStrLn $ name ++ " is defined"
                                      putStrLn $ name ++ " is recursively defined (decreasing on " ++
                                        showOrdinal i ++ " argument)"
                                    Ind name _ _ _ _ -> do
                                      putStrLnV 2 $ infoColor "**** inductive principle term defined ****"
                                      pPrintTopTm newctx
                                      putStrLnV 3 $ infoColor "**** inductive principle term defined (AST) ****"
                                      pPrintTopTmAST newctx
                                      putStrLnV 2 $ infoColor "**** inductive principle type defined ****"
                                      pPrintTopTy newctx
                                      putStrLnV 3 $ infoColor "**** inductive principle type defined (AST) ****"
                                      pPrintTopTyAST newctx
                                      putStrLn $ name ++ " is defined"
                                      putStrLn $ name ++ "_rect is defined"
                                  return newctx
                          
                    
            err -> do
              putStrLn $ errorColor "[ FAIL ] name checking"
              print err
              return ctx
