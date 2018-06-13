{-# LANGUAGE LambdaCase #-}
module MiniProver.TopLevel.ProofLoop where

import Text.Megaparsec
import MiniProver.Parser.Parser
import MiniProver.Core.Syntax
import MiniProver.Core.Context
import MiniProver.Core.Typing
import MiniProver.Core.Rename
import MiniProver.Core.SimplifyIndType
import MiniProver.PrettyPrint.PrettyPrint
import MiniProver.PrettyPrint.PrettyPrintAST
import MiniProver.PrettyPrint.Colorful
import MiniProver.TopLevel.Command
import MiniProver.Proof.ProofDef
import MiniProver.Proof.HandleTactic
import MiniProver.Proof.Build
import MiniProver.Proof.NameBounding
import MiniProver.Proof.Termination
import MiniProver.Proof.SimplifyIndType
import MiniProver.TopLevel.IO
import Control.Monad (forM)
import Debug.Trace

data ProofControl =
    UndoCmd
  | UndoOneCmd
  | UndoOKCmd
  | RestartCmd
  | AdmittedCmd
  | AbortCmd
  | QedCmd
  deriving (Show, Eq)

getProofCmd :: IO ProofCommand
getProofCmd = do
  inputStr <- getInputCommand
  let parsed = parse pproofcmd "" inputStr
  case parsed of
    Left err -> do
      print err
      getProofCmd
    Right cmd ->
      case cmd of
        Proof -> getProofCmd
        Undo -> do
          putStrLn "Can't perform undo"
          getProofCmd
        _ -> return cmd

proof :: Context -> Term -> IO (Either ProofControl Term)
proof ctx tm = do
  result <- proofList [Goal 0 ctx tm]
  case result of
    Left UndoCmd -> do
      putStrLn "Can't perform undo"
      proof ctx tm
    Left AbortCmd -> return $ Left AbortCmd
    Left RestartCmd -> proof ctx tm
    Left AdmittedCmd -> return $ Left AdmittedCmd
    Left UndoOneCmd -> proof ctx tm
    Right tm1 -> do
      putStrLn "No more subgoals"
      cmd <- getProofCmd
      case cmd of
        Restart -> proof ctx tm
        Admitted -> return (Left AdmittedCmd)
        Abort -> return (Left AbortCmd)
        Qed -> return $ Right (head tm1)

proofList :: [Goal] -> IO (Either ProofControl [Term])
proofList [] = return $ Right []
proofList glist@(g:gs) = do
  let rglist = map (\case Goal i ctx ty -> Goal i ctx (renameTerm ctx (simplifyIndType ty))) glist
  printGoals rglist
  r <- proofLoop g
  case r of
    Left UndoCmd -> return $ Left UndoOneCmd
    Left UndoOKCmd -> proofList glist
    Left QedCmd -> do
      putStrLn "not finished yet"
      proofList rglist
    Left cmd -> return $ Left cmd
    Right tm -> do
      tl <- proofList gs
      case tl of
        Left UndoOneCmd -> proofList glist
        Left UndoCmd -> proofList rglist
        Left cmd -> return $ Left cmd
        Right tmlst -> return $ Right (tm:tmlst)

proofLoop :: Goal -> IO (Either ProofControl Term)
proofLoop g@(Goal i ctx ty) = do
  input <- getInputCommand
  let proofinput = parse pproofinput "" input
  case proofinput of
    Left err -> do
      print err
      proofLoop g
    Right (PCmd Proof) -> proofLoop g
    Right (PCmd Undo) -> return (Left UndoCmd)
    Right (PCmd Restart) -> return (Left RestartCmd)
    Right (PCmd Admitted) -> return (Left AdmittedCmd)
    Right (PCmd Abort) -> return (Left AbortCmd)
    Right (PCmd Qed) -> do
      putStrLn "not finished yet"
      proofLoop g
    Right (PTac tac) ->
      case checkAllNameBoundedTactic ctx tac of
        AllNameBounded -> do
          let builttac = buildTactic tac ctx
          case computeDecParamTactic builttac of
            Left tm -> do
              putStrLn $ errorColor "[ FAIL ] termination checking"
              putStrLn "This term may not be terminating"
              prettyPrint tm
              proofLoop g
            Right tacWithDec ->
              case handleTactic g (simplifyIndTactic tacWithDec) of
                Left (TacticError str) -> do
                  putStrLn str
                  proofLoop g
                Right (Result goallst resultFunc) ->
                  let
                    f = do
                      rlst <- proofList goallst
                      case rlst of
                        Left UndoOneCmd -> return $ Left UndoOKCmd
                        Left cmd -> return $ Left cmd
                        Right tmlst ->
                          return $ Right $ resultFunc tmlst
                  in
                    f
        err -> do
          putStrLn $ errorColor "[ FAIL ] name checking"
          print err
          proofLoop g