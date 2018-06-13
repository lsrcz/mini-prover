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
  , pickFreshNameWithRejectList
  , pickFreshName
  , indexToName
  , nameToIndex
  , getBinding
  , getBindingType
  , getBindingTerm
  , getIndType
  , getIndTypeByConstr
  , getIndTypeTerm
  , getIndTypeType
  , getIndTypeConstrlst
  , getConstr
  , getConstrTerm
  , getConstrType
  , getConstrTypeI
  , getConstrIndTypeName
  ) where

import MiniProver.Core.Syntax
import MiniProver.Core.Subst
import Data.List (group, sort, concatMap, find, (\\), sortBy)
import Data.Maybe (fromMaybe)
import Data.Char (isDigit)

type Context = [(Name, Binding)]

data ContextError =
    IndexOutOfBound
  | UnboundName
  | IsTypeConstructor
  | IsConstructor
  | NotATypeConstructor
  | NotAConstructor
  | NotADefinition
  deriving (Eq, Show)

emptyContext :: Context
emptyContext = []

ctxLength :: Context -> Int
ctxLength = length

addBinding :: Context -> Name -> Binding -> Context
addBinding ctx name bind = (name,bind) : ctx

addName :: Context -> Name -> Context
addName ctx name = addBinding ctx name NameBind

deleteTilde :: String -> String
deleteTilde n@(x:xs) = if x == '~' then xs else n

isNameBound :: Context -> Name -> Bool
isNameBound ctx name =
  let
    nameBoundInBinding :: (Name, Binding) -> Bool
    nameBoundInBinding (n,b) =
      deleteTilde name == deleteTilde n ||
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
checkDuplicateGlobalName ctx (Theorem name _) =
  [ name | isNameBound ctx name ]
checkDuplicateGlobalName _ (Check _) = []

removeTailDigits :: Name -> Name
removeTailDigits [] = []
removeTailDigits ls@(x:xs) =
  case removeTailDigits xs of
    [] -> if isDigit x then [] else [x]
    _ -> ls

pickFreshNameWithRejectList :: Context -> [Name] -> Name -> (Context, Name)
pickFreshNameWithRejectList ctx lst oldname =
  let
    name = removeTailDigits oldname
  in
    if isNameBound ctx name || name `elem` lst
      then pickFreshNameWithRejectList' ctx lst name 0
      else ((name,NameBind) : ctx, name)

pickFreshNameWithRejectList' :: Context -> [Name] -> Name -> Int -> (Context, Name)
pickFreshNameWithRejectList' ctx lst name i =
  let
    newname = name ++ show i
  in
    if isNameBound ctx newname || newname `elem` lst
      then pickFreshNameWithRejectList' ctx lst name (i + 1)
      else ((newname,NameBind) : ctx, newname)


pickFreshName :: Context -> Name -> (Context, Name)
pickFreshName ctx oldname =
  let
    name = removeTailDigits oldname
  in
    if isNameBound ctx name
      then pickFreshName' ctx name 0
      else ((name,NameBind) : ctx, name)
  
pickFreshName' :: Context -> Name -> Int -> (Context, Name)
pickFreshName' ctx name i =
  let
    newname = name ++ show i
  in
    if isNameBound ctx newname
      then pickFreshName' ctx name (i + 1)
      else ((newname,NameBind) : ctx, newname)

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

getBindingTerm :: Context -> Index -> Either ContextError Term
getBindingTerm ctx idx =
  case getBinding ctx idx of
    Left err -> Left err
    Right (TmAbbBind _ (Just tm)) -> Right tm
    Right (TmAbbBind _ Nothing) -> Left NotADefinition
    _ -> error "This should not happen"

getIndType :: Context -> Name -> Either ContextError (Int, Term, Term, [Constructor])
getIndType [] _ = Left NotATypeConstructor
getIndType ((nameb,binder):xs) name =
  case binder of
    IndTypeBind i ty tm constrlst
      | nameb == name -> Right (i, ty, tm, constrlst)
    _ -> getIndType xs name

getIndTypeByConstr :: Context -> Name -> Either ContextError (Name, Int, Term, Term, [Constructor])
getIndTypeByConstr [] _ = Left NotAConstructor
getIndTypeByConstr ((namei,binder):xs) name =
  case binder of
    IndTypeBind i ty tm constrlst
      | any (\case Constructor namec _ _ -> name == namec) constrlst -> Right (namei, i, ty, tm, constrlst)
    _ -> getIndTypeByConstr xs name

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

getConstrTypeI :: Context -> Name -> Either ContextError Int
getConstrTypeI [] name = Left NotAConstructor
getConstrTypeI ((_,binder):xs) name =
  case binder of
    IndTypeBind i _ _ constrlst ->
      if any (\case Constructor cname _ _ -> cname == name) constrlst
        then
          Right i
        else
          getConstrTypeI xs name
    _ -> getConstrTypeI xs name

getConstrIndTypeName :: Context -> Name -> Either ContextError String
getConstrIndTypeName [] name = Left NotAConstructor
getConstrIndTypeName ((idname,binder):xs) name =
  case binder of
    IndTypeBind i _ _ constrlst ->
      if any (\case Constructor cname _ _ -> cname == name) constrlst
        then
          Right idname
        else
          getConstrIndTypeName xs name
    _ -> getConstrIndTypeName xs name

