{-# LANGUAGE LambdaCase #-}
module MiniProver.PrettyPrint (
    prettyShow
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
prettyShow' (TmFix (TmLambda _ _ tm)) indent = "fix " ++ prettyShow' tm indent
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
prettyShow' (TmMatch tm names ty equlst) indent = 
  "match " ++ prettyShow' tm indent ++ " in " ++ unwords names ++
  " return " ++ prettyShow' ty indent ++ " with " ++ 
  concatMap 
    (\case 
      Equation names' tm' -> 
        indentNewline (indent + 2) ++ "| " ++ unwords names' ++
        " => " ++ prettyShow' tm' (indent + 4))
    equlst