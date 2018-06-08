{-# LANGUAGE LambdaCase #-}
module MiniProver.PrettyPrint.PrettyPrint (
    prettyShow
  , prettyPrint
  , prettyShowCommand
  , prettyPrintCommand
  , addIndent
  ) where

import MiniProver.Core.Syntax
import MiniProver.Core.Context
import MiniProver.PrettyPrint.Colorful
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

prettyFixTail :: Term -> Term -> Int -> String
prettyFixTail (TmProd _ _ tmp) (TmLambda name ty tml) indent =
  " (" ++ name ++ ":" ++ prettyShow' ty indent ++ ")" ++ prettyFixTail tmp tml indent
prettyFixTail tmp tml indent =
  " : " ++ prettyShow' tmp indent ++ " := " ++ indentNewline indent ++ prettyShow' tml indent

prettyFix :: Term -> Int -> String
prettyFix (TmFix _ (TmLambda name tmp tml)) indent =
  frontGroundColor BWHITE (bright "fix ") ++ name ++ prettyFixTail tmp tml (indent + 2)

prettyShow' :: Term -> Int -> String
prettyShow' (TmRel name _) _ = name
prettyShow' (TmVar name) _ = name
prettyShow' (TmAppl lst) indent = 
  unwords $ map (`addParens` indent) lst
prettyShow' (TmProd name ty tm) indent =
  if head name == '_' 
    then addParens ty indent ++ " -> " ++ addParens tm indent
    else frontGroundColor BWHITE (bright "forall ") ++ "(" ++ name ++ ":" ++ prettyShow' ty indent ++
         ")" ++ prettyForallTail tm (indent + 2)
prettyShow' (TmLambda name ty tm) indent =
  frontGroundColor BWHITE (bright "fun ") ++ "(" ++ name ++ ":" ++ prettyShow' ty indent ++
  ")" ++ prettyLambdaTail tm (indent + 2)
prettyShow' origtm@(TmFix _ TmLambda{}) indent = prettyFix origtm indent -- "fix " ++ prettyShow' tm indent
prettyShow' (TmLetIn name ty tm bdy) indent = 
  frontGroundColor BWHITE (bright "let ") ++ name ++ " : " ++ prettyShow' ty indent ++
  " := " ++ prettyShow' tm indent ++ frontGroundColor BWHITE (bright " in ") ++
  prettyShow' bdy indent
prettyShow' (TmIndType name tmlst) indent = 
  unwords $ frontGroundColor BGREEN name : map (`addParens` indent) tmlst
prettyShow' (TmConstr name tmlst) indent = 
  unwords $ frontGroundColor BGREEN name : map (`addParens` indent) tmlst
prettyShow' TmType _ = frontGroundColor YELLOW (bright "Type")
prettyShow' TmTypeHigher _ = frontGroundColor YELLOW (bright "TypeH")
prettyShow' (TmMatch _ tm name names ty equlst) indent = 
  frontGroundColor BWHITE (bright "match ") ++ prettyShow' tm indent ++
  frontGroundColor BWHITE (bright " as ") ++ name ++
  frontGroundColor BWHITE (bright " in ") ++ unwords names ++
  frontGroundColor BWHITE (bright " return ") ++ prettyShow' ty indent ++
  frontGroundColor BWHITE (bright " with ") ++ 
  concatMap 
    (\case 
      Equation names' tm' -> 
        indentNewline (indent + 2) ++ "| " ++ unwords names' ++
        " => " ++ prettyShow' tm' (indent + 4))
    equlst ++ indentNewline indent ++ frontGroundColor BWHITE (bright "end")

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
prettyShowCommand (Ax name ty) = frontGroundColor RED (bright "Axiom ") ++ name ++ " : " ++ prettyShow ty
prettyShowCommand (Def name ty tm) = frontGroundColor RED (bright "Definition ") ++ name ++ prettyDefinitionTail ty tm
prettyShowCommand (Ind name n ty _ constrlst) = frontGroundColor RED (bright "Inductive ") ++ name ++ prettyInductiveTyTail n ty ++ prettyConstrLst n constrlst
prettyShowCommand (Fix name (TmFix _ (TmLambda _ ty tm))) = frontGroundColor RED (bright "Fixpoint ") ++ name ++ prettyDefinitionTail ty tm
prettyShowCommand (Theorem name ty) = frontGroundColor RED (bright "Theorem ") ++ name ++ " : " ++ prettyShow ty

prettyPrintCommand :: Command -> IO ()
prettyPrintCommand cmd = putStrLn $ prettyShowCommand cmd

addIndent :: Int -> String -> String
addIndent i = unlines . map (\x -> replicate i ' ' ++ x) . lines