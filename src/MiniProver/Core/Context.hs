{-# LANGUAGE LambdaCase #-}
module MiniProver.Core.Context (
    Context
  , ContextError(..)
  , emptyContext
  , ctxLength
  , addBinding
  , addName
  , isNameBound
  , checkDuplicateGlobalName
  , pickFreshName
  , indexToName
  , nameToIndex
  , getBinding
  , getBindingType
  , getIndType
  , getIndTypeTerm
  , getIndTypeType
  , getIndTypeConstrlst
  , getConstrTerm
  , getConstrType
  ) where

import MiniProver.Core.Syntax
import MiniProver.Core.Subst
import Data.List (group, sort, concatMap, find, (\\), sortBy)
import Data.Maybe (fromMaybe)

type Context = [(Name, Binding)]

data ContextError =
    IndexOutOfBound
  | UnboundName
  | IsTypeConstructor
  | IsConstructor
  | NotATypeConstructor
  | NotAConstructor
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
            any (\case Constructor namei _ _ -> namei == name) lst
          _ -> False
  in
    any nameBoundInBinding ctx

checkDuplicateGlobalName :: Context -> Command -> [Name]
checkDuplicateGlobalName ctx (Ax name _) =
  [ name | isNameBound ctx name ]
checkDuplicateGlobalName ctx (Def name _ _) =
  [ name | isNameBound ctx name ]
checkDuplicateGlobalName ctx (Ind name _ _ _ constrlst) =
  [ xname | xname <- name : map (\(n,_,_) -> n) constrlst, isNameBound ctx xname]
checkDuplicateGlobalName ctx (Fix name _) =
  [ name | isNameBound ctx name ]
  
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

getBinding :: Context -> Index -> Either ContextError Binding
getBinding ctx idx =
  if ctxLength ctx > idx
    then Right $ bindingShift (idx + 1) $ snd $ ctx !! idx
    else Left IndexOutOfBound

getBindingType :: Context -> Index -> Either ContextError Term
getBindingType ctx idx =
  case getBinding ctx idx of
    Left err -> Left err
    Right (VarBind ty) -> Right ty
    Right (TmAbbBind ty _) -> Right ty
    _ -> error "This should not happen"

getIndType :: Context -> Name -> Either ContextError (Int, Term, Term, [Constructor])
getIndType [] _ = Left NotATypeConstructor
getIndType ((nameb,binder):xs) name =
  case binder of
    IndTypeBind i ty tm constrlst
      | nameb == name -> Right (i, ty, tm, constrlst)
    _ -> getIndType xs name

getIndTypeTerm :: Context -> Name -> Either ContextError Term
getIndTypeTerm ctx name = (\(_,_,tm,_) -> tm) <$> getIndType ctx name

getIndTypeType :: Context -> Name -> Either ContextError (Int, Term)
getIndTypeType ctx name = (\(i,ty,_,_) -> (i,ty)) <$> getIndType ctx name

getIndTypeConstrlst :: Context -> Name -> Either ContextError [Constructor]
getIndTypeConstrlst ctx name = (\(_,_,_,constrlst) -> constrlst) <$> getIndType ctx name

getConstr :: Context -> Name -> Either ContextError (Term, Term)
getConstr [] name = Left NotAConstructor
getConstr ((_,binder):xs) name =
  case binder of
    IndTypeBind _ _ _ constrlst ->
      maybe (getConstr xs name) (Right . (\case Constructor _ ty tm -> (ty, tm))) $ 
        find (\case Constructor namec _ _ -> name == namec) constrlst
    _ -> getConstr xs name

getConstrTerm :: Context -> Name -> Either ContextError Term
getConstrTerm ctx name = snd <$> getConstr ctx name

getConstrType :: Context -> Name -> Either ContextError Term
getConstrType ctx name = fst <$> getConstr ctx name

