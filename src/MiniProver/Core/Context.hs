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
  any (\(n,_) -> name == n) ctx
  
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
nameToIndex ctx name =
  case findIndex ((==name) . fst) ctx of
    Nothing -> Left UnboundName
    Just idx -> Right idx

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
checkAllNameBounded ctx (TmMatch tm equlst) = 
  unique $ sort $
    checkAllNameBounded ctx tm ++
    concatMap (checkAllNameBoundedEqu ctx) equlst

checkAllNameBoundedEqu :: Context -> Equation -> [String]
checkAllNameBoundedEqu ctx (Equation namelst tm) =
  checkAllNameBounded (foldl addName ctx (tail namelst)) tm

