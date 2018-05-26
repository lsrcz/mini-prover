{-# LANGUAGE LambdaCase #-}
module MiniProver.PrettyPrint.PrettyPrint (
    prettyShow
  , prettyPrint
  , prettyShowCommand
  , prettyPrintCommand
  ) where

import MiniProver.Core.Syntax
import MiniProver.Core.Context
import Data.String (unwords)

isAtom :: Term -> Bool
isAtom (TmRel _ _) = True
isAtom (TmVar _) = True
isAtom (TmIndType _ []) = True
isAtom (TmConstr _ []) = True
isAtom TmType = True
isAtom TmTypeHigher = True
isAtom _ = False

addParens :: Term -> Int -> String
addParens tm indent =
  if isAtom tm
    then prettyShow' tm indent
    else "(" ++ prettyShow' tm indent ++ ")"

indentNewline :: Int -> String
indentNewline i = "\n" ++ replicate i ' '

prettyPrint :: Term -> IO ()
prettyPrint tm = putStrLn $ prettyShow tm

prettyShow :: Term -> String
prettyShow tm = prettyShow' tm 0

prettyForallTail :: Term -> Int -> String
prettyForallTail (TmProd name ty tm) indent =
  " (" ++ name ++ ":" ++ prettyShow' ty indent ++ ")" ++ prettyForallTail tm indent
prettyForallTail tm indent =
  "," ++ indentNewline indent ++ prettyShow' tm indent

prettyLambdaTail :: Term -> Int -> String
prettyLambdaTail (TmLambda name ty tm) indent =
  " (" ++ name ++ ":" ++ prettyShow' ty indent ++ ")" ++ prettyLambdaTail tm indent
prettyLambdaTail tm indent =
  " => " ++ indentNewline indent ++ prettyShow' tm indent

prettyFix :: Term -> Int -> String
prettyFix (TmFix _ (TmLambda name _ tm)) indent = "fix " ++ name ++ prettyLambdaTail tm (indent + 2)

prettyShow' :: Term -> Int -> String
prettyShow' (TmRel name _) _ = name
prettyShow' (TmVar name) _ = name
prettyShow' (TmAppl lst) indent = 
  unwords $ map (`addParens` indent) lst
prettyShow' (TmProd name ty tm) indent =
  if head name == '_' 
    then addParens ty indent ++ " -> " ++ addParens tm indent
    else "forall " ++ "(" ++ name ++ ":" ++ prettyShow' ty indent ++
         ")" ++ prettyForallTail tm (indent + 2)
prettyShow' (TmLambda name ty tm) indent =
  "fun " ++ "(" ++ name ++ ":" ++ prettyShow' ty indent ++
  ")" ++ prettyLambdaTail tm (indent + 2)
prettyShow' origtm@(TmFix _ TmLambda{}) indent = prettyFix origtm indent -- "fix " ++ prettyShow' tm indent
prettyShow' (TmLetIn name ty tm bdy) indent = 
  "let " ++ name ++ " : " ++ prettyShow' ty indent ++
  " := " ++ prettyShow' tm indent ++ " in " ++
  prettyShow' bdy indent
prettyShow' (TmIndType name tmlst) indent = 
  unwords $ name : map (`addParens` indent) tmlst
prettyShow' (TmConstr name tmlst) indent = 
  unwords $ name : map (`addParens` indent) tmlst
prettyShow' TmType _ = "Type"
prettyShow' TmTypeHigher _ = "TypeH"
prettyShow' (TmMatch _ tm name names ty equlst) indent = 
  "match " ++ prettyShow' tm indent ++ " as " ++ name ++ " in " ++ unwords names ++
  " return " ++ prettyShow' ty indent ++ " with " ++ 
  concatMap 
    (\case 
      Equation names' tm' -> 
        indentNewline (indent + 2) ++ "| " ++ unwords names' ++
        " => " ++ prettyShow' tm' (indent + 4))
    equlst ++ indentNewline (indent + 2) ++ "end"

prettyDefinitionTail :: Term -> Term -> String
prettyDefinitionTail ty@(TmProd namety tyty tmty) tm@(TmLambda nametm tytm tmtm)
  | namety == nametm && tyty == tytm =
      " (" ++ namety ++ ":" ++ prettyShow' tyty 0 ++ ")" ++ prettyDefinitionTail tmty tmtm
prettyDefinitionTail ty tm =
  " : " ++ prettyShow' ty 0 ++ " :=" ++ indentNewline 2 ++ prettyShow' tm 2

prettyInductiveTyTail :: Int -> Term -> String
prettyInductiveTyTail n (TmProd name ty tm)
  | n > 0 = " (" ++ name ++ ":" ++ prettyShow' ty 0 ++ ")" ++ prettyInductiveTyTail (n-1) tm
prettyInductiveTyTail _ tm = " : " ++ prettyShow' tm 0 ++ " :="

prettyConstrTyTail :: Int -> Int -> Term -> String
prettyConstrTyTail l n (TmProd _ _ tm)
  | n > 0 = prettyConstrTyTail l (n - 1) tm
prettyConstrTyTail l _ tm = prettyShow' tm (l + 7)

prettyConstrLst :: Int -> [(Name,Term,Term)] -> String
prettyConstrLst _ [] = ""
prettyConstrLst n ((name,ty,_):xs) = indentNewline 2 ++ "| " ++ name ++ " : " ++ prettyConstrTyTail (length name) n ty ++ prettyConstrLst n xs

prettyShowCommand :: Command -> String
prettyShowCommand (Ax name ty) = "Axiom " ++ name ++ " : " ++ prettyShow ty
prettyShowCommand (Def name ty tm) = "Definition " ++ name ++ prettyDefinitionTail ty tm
prettyShowCommand (Ind name n ty _ constrlst) = "Inductive " ++ name ++ prettyInductiveTyTail n ty ++ prettyConstrLst n constrlst
prettyShowCommand (Fix name (TmFix _ (TmLambda _ ty tm))) = "Fixpoint " ++ name ++ prettyDefinitionTail ty tm

prettyPrintCommand :: Command -> IO ()
prettyPrintCommand cmd = putStrLn $ prettyShowCommand cmd