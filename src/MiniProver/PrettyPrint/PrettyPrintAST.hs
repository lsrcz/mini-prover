module MiniProver.PrettyPrint.PrettyPrintAST (
    prettyShowAST
  , prettyPrintAST
  , prettyShowCommandAST
  , prettyPrintCommandAST
  ) where

import MiniProver.Core.Syntax
import Data.String (unlines)

isAtom :: Term -> Bool
isAtom TmType = True
isAtom TmTypeHigher = True
isAtom _ = False

addLeftParens :: String -> Char -> String
addLeftParens str parens = snd $ go str
  where
    go :: String -> (Int, String)
    go [] = (0, "")
    go str@(x:xs) =
      if x /= ' '
        then (0, str)
        else
          let
            (i, str) = go xs
          in 
            if i == 1
              then (2, parens:xs)
              else (i + 1, x:str)

addRightParens :: String -> Char -> String
addRightParens [] _ = []
addRightParens str parens =
  if last str `elem` ")]" then str ++ [parens] else str ++ (' ':[parens])

addParens :: [String] -> Char -> Char -> [String]
addParens strlst lparen rparen =
  if length strlst >= 2
    then
      let
        hd = head strlst
        ls = last strlst
        mid = tail $ init strlst
      in
        addLeftParens hd lparen : (mid ++ [addRightParens ls rparen])
    else
      let
        hd = head strlst
      in
        [addRightParens (addLeftParens hd lparen) rparen]

spaces :: Int -> String
spaces i = replicate i ' '

prettyPrintAST :: Term -> IO ()
prettyPrintAST tm = putStrLn $ prettyShowAST tm

prettyShowAST :: Term -> String
prettyShowAST tm = unlines $ prettyShowAST' tm 2

-- assert not empty
prettyShowTermList :: [Term] -> Int -> [String]
prettyShowTermList tmlst indent = 
  prettyShowAST' (head tmlst) indent ++
  concatMap 
    (\tm ->
      case prettyShowAST' tm indent of
        (h:t) -> addLeftParens h ',' : t) (tail tmlst)

prettyShowNameList :: [Name] -> Int -> [String]
prettyShowNameList namelst indent =
  (spaces indent ++ show (head namelst)) :
  map ((`addLeftParens` ',') . (spaces indent ++) .show) (tail namelst)

prettyShowEquationList :: [Equation] -> Int -> [String]
prettyShowEquationList equlst indent =
  prettyShowEquation (head equlst) indent ++
  concatMap
    (\eq ->
      case prettyShowEquation eq indent of
        (h:t) -> addLeftParens h ',' : t) (tail equlst)

prettyShowEquation :: Equation -> Int -> [String]
prettyShowEquation (Equation namelst tm) indent = (spaces indent ++ "Equation") :
  ( addParens (prettyShowNameList namelst (indent + 2)) '[' ']' ++
    prettyShowAddParensNonAtom tm (indent + 2))

prettyShowAddParensNonAtom :: Term -> Int -> [String]
prettyShowAddParensNonAtom tm indent =
  if isAtom tm then prettyShowAST' tm indent else addParens (prettyShowAST' tm indent) '(' ')'

prettyShowAST' :: Term -> Int -> [String]
prettyShowAST' (TmRel name idx) indent = [spaces indent ++ "TmRel " ++ show name ++ " " ++ show idx]
prettyShowAST' (TmVar name) indent = [spaces indent ++ "TmVar " ++ show name]
prettyShowAST' (TmAppl tmlst) indent = (spaces indent ++ "TmAppl") :
  addParens (prettyShowTermList tmlst (indent + 2)) '[' ']'
prettyShowAST' (TmProd name ty tm) indent = (spaces indent ++ "TmProd " ++ show name) :
  ( prettyShowAddParensNonAtom ty (indent + 2) ++ prettyShowAddParensNonAtom tm (indent + 2))
prettyShowAST' (TmLambda name ty tm) indent = (spaces indent ++ "TmLambda " ++ show name) :
  ( prettyShowAddParensNonAtom ty (indent + 2) ++ prettyShowAddParensNonAtom tm (indent + 2))
prettyShowAST' (TmFix n tm) indent = (spaces indent ++ "TmFix " ++ if n >= 0 then show n else "(" ++ show n ++ ")") :
  addParens (prettyShowAST' tm (indent + 2)) '(' ')'
prettyShowAST' (TmLetIn name ty tm bdy) indent = (spaces indent ++ "TmLetIn " ++ show name) :
  ( prettyShowAddParensNonAtom ty (indent + 2) ++ 
    prettyShowAddParensNonAtom tm (indent + 2) ++
    prettyShowAddParensNonAtom bdy (indent + 2))
prettyShowAST' (TmIndType name tmlst) indent =
  if null tmlst
    then
      [spaces indent ++ "TmIndType " ++ show name ++ " []"]
    else
      (spaces indent ++ "TmIndType " ++ show name) :
        addParens (prettyShowTermList tmlst (indent + 2)) '[' ']'
prettyShowAST' (TmConstr name tmlst) indent = 
  if null tmlst
    then
      [spaces indent ++ "TmConstr " ++ show name ++ " []"]
    else
      (spaces indent ++ "TmConstr " ++ show name) :
        addParens (prettyShowTermList tmlst (indent + 2)) '[' ']'
prettyShowAST' TmType indent = [spaces indent ++ "TmType"]
prettyShowAST' TmTypeHigher indent = [spaces indent ++ "TmTypeHigher"]

prettyShowAST' (TmMatch n tm name namelst ty equlst) indent =
  ( spaces indent ++ "TmMatch " ++ if n == (-1) then "(-1)" else show n) :
  ( prettyShowAddParensNonAtom tm (indent + 2) ++
    [spaces (indent + 2) ++ show name] ++
    addParens (prettyShowNameList namelst (indent + 2)) '[' ']' ++
    prettyShowAddParensNonAtom ty (indent + 2) ++
    addParens (prettyShowEquationList equlst (indent + 2)) '[' ']' )

prettyPrintCommandAST :: Command -> IO ()
prettyPrintCommandAST cmd = putStrLn $ prettyShowCommandAST cmd

prettyShowCommandAST :: Command -> String
prettyShowCommandAST cmd = unlines $ prettyShowCommandAST' cmd 2

prettyShowCommandAST' :: Command -> Int -> [String]
prettyShowCommandAST' (Ax name tm) indent = (spaces indent ++ "Ax " ++ show name) :
  prettyShowAddParensNonAtom tm (indent + 2)
prettyShowCommandAST' (Def name ty tm) indent = (spaces indent ++ "Def " ++ show name) :
  ( prettyShowAddParensNonAtom ty (indent + 2) ++ prettyShowAddParensNonAtom tm (indent + 2))
prettyShowCommandAST' (Ind name i ty tm constrlst) indent =
  ( spaces indent ++ "Ind " ++ show name ++ " " ++ show i ) :
  ( prettyShowAddParensNonAtom ty (indent + 2) ++
    prettyShowAddParensNonAtom tm (indent + 2) ++
    addParens (prettyShowConstrList constrlst (indent + 2)) '[' ']')
prettyShowCommandAST' (Fix name tm) indent = (spaces indent ++ "Fix " ++ show name) :
  prettyShowAddParensNonAtom tm (indent + 2)

prettyShowConstr :: (Name, Term, Term) -> Int -> [String]
prettyShowConstr (name, ty, tm) indent = (spaces indent ++ show name) :
  ( ( case prettyShowAST' ty indent of
        (h:t) -> addLeftParens h ',' : t) ++
    ( case prettyShowAST' tm indent of
        (h:t) -> addLeftParens h ',' : t))

prettyShowConstrList :: [(Name, Term, Term)] -> Int -> [String]
prettyShowConstrList constrlst indent =
  addParens (prettyShowConstr (head constrlst) (indent + 2)) '(' ')' ++
  concatMap
    (\constr ->
      case addParens (prettyShowConstr constr (indent + 2)) '(' ')' of
        (h:t) -> addLeftParens h ',' : t) (tail constrlst)