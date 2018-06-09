{-# LANGUAGE LambdaCase #-}
module MiniProver.PrettyPrint.PrintingCommand where

import MiniProver.Core.Syntax
import MiniProver.Core.Context
import MiniProver.PrettyPrint.PrettyPrint
import Data.Either (fromRight)

printIndType :: Name -> (Int, Term, Term, [Constructor]) -> IO ()
printIndType nm (i,ty,tm,constrlst) =
  prettyPrintCommand (Ind nm i ty tm $
    map (\case Constructor nmc tyc tmc -> (nmc,tyc,tmc)) constrlst)

processPrint :: Context -> Name -> IO ()
processPrint ctx nm =
  case nameToIndex ctx nm of
    Left UnboundName -> putStrLn $ "Unbound name " ++ nm
    Left IsTypeConstructor ->
      printIndType nm $ fromRight (error "This should not happen") $ getIndType ctx nm
    Left IsConstructor ->
      case getIndTypeByConstr ctx nm of
        Right (nm1,i,ty,tm,constrlst) -> printIndType nm1 (i,ty,tm,constrlst)
        Left _ -> error "This should not happen"
    Right idx ->
      let processTystr tystr = "     : " ++ drop 7 (addIndent 7 tystr) in
      case getBinding ctx idx of
        Right (TmAbbBind ty Nothing) -> do
          putStrLn $ nm ++ " = [****]"
          putStrLn $ processTystr $ prettyShow ty
        Right (VarBind ty) -> do
          putStrLn $ nm ++ " = [****]"
          putStrLn $ processTystr $ prettyShow ty
        Right (TmAbbBind ty (Just tm)) -> do
          putStrLn $ nm ++ " ="
          prettyPrint tm
          putStrLn $ processTystr $ prettyShow ty
        Left _ -> error "This should not happen"


      