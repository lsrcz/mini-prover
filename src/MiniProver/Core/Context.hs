{-# LANGUAGE LambdaCase #-}
module MiniProver.Core.Context (
    Context
  , ContextError(..)
  , emptyContext
  , ctxLength
  , addBinding
  , addName
  , isNameBound
  , pickFreshName
  , indexToName
  , nameToIndex
  , indexToBinding
  , checkAllNameBounded
  ) where

import MiniProver.Core.Syntax
import Data.List (findIndex, group, sort, concatMap)

type Context = [(Name, Binding)]

data ContextError =
    IndexOutOfBound
  | UnboundName
  | IsTypeConstructor
  | IsConstructor
  deriving (Eq, Show)

emptyContext :: Context
emptyContext = []

ctxLength :: Context -> Int
ctxLength = length

addBinding :: Context -> Name -> Binding -> Context
addBinding ctx name bind = (name,bind) : ctx

addName :: Context -> Name -> Context
addName ctx name = addBinding ctx name NameBind

isNameBound :: Context -> Name -> Bool
isNameBound ctx name =
  let
    nameBoundInBinding :: (Name, Binding) -> Bool
    nameBoundInBinding (n,b) =
      name == n ||
        case b of
          IndTypeBind _ _ _ lst ->
            any (\case Constructor namei _ _ -> namei == n) lst
          _ -> False
  in
    any nameBoundInBinding ctx
  
pickFreshName :: Context -> Name -> (Context, Name)
pickFreshName ctx name =
  if isNameBound ctx name
    then pickFreshName ctx (name ++ "'")
    else ((name,NameBind) : ctx, name)

indexToName :: Context -> Index -> Either ContextError Name
indexToName ctx idx =
  if ctxLength ctx > idx
    then Right $ fst $ ctx !! idx
    else Left IndexOutOfBound

nameToIndex :: Context -> Name -> Either ContextError Index
nameToIndex [] _ = Left UnboundName
nameToIndex ((nameb,binder):xs) name =
  case binder of
    IndTypeBind _ _ _ constrlst
      | nameb == name -> Left IsTypeConstructor
      | any (\case Constructor namec _ _ -> name == namec) constrlst ->
          Left IsConstructor
      | otherwise -> (+1) <$> nameToIndex xs name
    _
      | nameb == name -> Right 0
      | otherwise -> (+1) <$> nameToIndex xs name

indexToBinding :: Context -> Index -> Either ContextError Binding
indexToBinding ctx idx =
  if ctxLength ctx > idx
    then Right $ snd $ ctx !! idx
    else Left IndexOutOfBound

unique :: (Eq a) => [a] -> [a]
unique = map head . group

checkAllNameBounded :: Context -> Term -> [String]
checkAllNameBounded _ (TmRel _ _) = error "This should not happen"
checkAllNameBounded ctx (TmVar name) = if isNameBound ctx name then [] else [name]
checkAllNameBounded ctx (TmAppl lst) = 
  unique $ sort $ concatMap (checkAllNameBounded ctx) lst
checkAllNameBounded ctx (TmProd name ty tm) = 
  unique $ sort $ 
    checkAllNameBounded ctx ty ++ 
    checkAllNameBounded (addName ctx name) tm
checkAllNameBounded ctx (TmLambda name ty tm) =
  unique $ sort $ 
    checkAllNameBounded ctx ty ++ 
    checkAllNameBounded (addName ctx name) tm
checkAllNameBounded ctx (TmFix tm) = checkAllNameBounded ctx tm
checkAllNameBounded ctx (TmLetIn name ty tm bdy) =
  unique $ sort $ 
    checkAllNameBounded ctx ty ++ 
    checkAllNameBounded ctx tm ++
    checkAllNameBounded (addName ctx name) bdy
checkAllNameBounded _ (TmIndType _ _) = error "This should not happen"
checkAllNameBounded _ (TmSort _) = []
checkAllNameBounded ctx (TmMatch tm namelst rty equlst) = 
  unique $ sort $
    checkAllNameBounded ctx tm ++
    checkAllNameBounded (foldl addName ctx (tail namelst)) rty ++
    concatMap (checkAllNameBoundedEqu ctx) equlst

checkAllNameBoundedEqu :: Context -> Equation -> [String]
checkAllNameBoundedEqu ctx (Equation namelst tm) =
  checkAllNameBounded (foldl addName ctx (tail namelst)) tm

