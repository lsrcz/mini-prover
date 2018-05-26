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
  , getBinding
  , getBindingType
  , getIndType
  , getIndTypeTerm
  , getIndTypeType
  , getIndTypeConstrlst
  , getConstrTerm
  , getConstrType
  , NameBoundStatus(..)
  , checkAllNameBounded
  , checkAllNameBoundedCommand
  ) where

import MiniProver.Core.Syntax
import MiniProver.Core.Subst
import Data.List (group, sort, concatMap, find, (\\), sortBy)
import Data.Maybe (fromMaybe)
import Debug.Trace

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

unique :: (Eq a) => [a] -> [a]
unique = map head . group

data NameBoundStatus =
    NoIndTypeProvided Term 
  | UnknownIndType Term Name
  | WrongNumParamsInTypeMatching Term [Name]
  | UnusedNameInTypeMatching Term [Name]
  | DuplicateNameInTypeMatching Term [Name]
  | UnknownConstr Term [Name]
  | DuplicateConstr Term [Name]
  | InsufficientConstrs Term [Name]
  | WrongNumParamsInConstrMatching Term [Name]
  | UnusedNameInConstrMatching Term [Name] [Name]
  | DuplicateNameInConstrMatching Term [Name] [Name]
  | UnboundNameInTerm [Name]
  | AllNameBounded
  deriving (Show, Eq)

uniqueSort :: (Ord a) => [a] -> [a]
uniqueSort = unique . sort

sortNameBoundStatus :: NameBoundStatus -> NameBoundStatus
sortNameBoundStatus (UnusedNameInTypeMatching term nmlst) =
  UnusedNameInTypeMatching term $ uniqueSort nmlst
sortNameBoundStatus (DuplicateNameInTypeMatching term nmlst) =
  DuplicateNameInTypeMatching term $ uniqueSort nmlst
sortNameBoundStatus (UnknownConstr term nmlst) =
  UnknownConstr term $ uniqueSort nmlst
sortNameBoundStatus (DuplicateConstr term nmlst) =
  DuplicateConstr term $ uniqueSort nmlst
sortNameBoundStatus (InsufficientConstrs term nmlst) =
  InsufficientConstrs term $ uniqueSort nmlst
sortNameBoundStatus (UnusedNameInConstrMatching term constrnmlst nmlst) =
  UnusedNameInConstrMatching term constrnmlst $ uniqueSort nmlst
sortNameBoundStatus (DuplicateNameInConstrMatching term constrnmlst nmlst) =
  DuplicateNameInConstrMatching term constrnmlst $ uniqueSort nmlst
sortNameBoundStatus (UnboundNameInTerm nmlst) =
  UnboundNameInTerm $ uniqueSort nmlst
sortNameBoundStatus nbs = nbs

combineNameBoundStatus :: [NameBoundStatus] -> NameBoundStatus
combineNameBoundStatus [] = AllNameBounded
combineNameBoundStatus (AllNameBounded:xs) =
  sortNameBoundStatus $ combineNameBoundStatus xs
combineNameBoundStatus (UnboundNameInTerm nmlst:xs) =
  case combineNameBoundStatus xs of
    UnboundNameInTerm nmlst1 -> sortNameBoundStatus $ UnboundNameInTerm (nmlst ++ nmlst1)
    AllNameBounded -> UnboundNameInTerm nmlst
    nbs -> sortNameBoundStatus nbs
combineNameBoundStatus (nbs:xs) = sortNameBoundStatus nbs

checkNameLst :: Int -> [Name] -> [Int]
checkNameLst n lst = go 1 lst
  where
    go :: Int -> [Name] -> [Int]
    go i [] = []
    go i (x:xs)
      | i > n = []
      | x == "_" = go (i + 1) xs
      | otherwise = i : go (i + 1) xs

countParams :: Term -> Int
countParams (TmProd _ _ tm) = 1 + countParams tm
countParams _ = 0

checkAllNameBounded :: Context -> Term -> NameBoundStatus
checkAllNameBounded _ (TmRel _ _) =
  error "This should not happen: checkAllNameBound TmRel"
checkAllNameBounded ctx (TmVar name) =
  if isNameBound ctx name then AllNameBounded else UnboundNameInTerm [name]
checkAllNameBounded ctx (TmAppl lst) = 
  combineNameBoundStatus $ map (checkAllNameBounded ctx) lst
checkAllNameBounded ctx (TmProd name ty tm) =
  combineNameBoundStatus
    [ checkAllNameBounded ctx ty,
      checkAllNameBounded (addName ctx name) tm ]
checkAllNameBounded ctx (TmLambda name ty tm) =
  combineNameBoundStatus
    [ checkAllNameBounded ctx ty,
       checkAllNameBounded (addName ctx name) tm ]
checkAllNameBounded ctx (TmFix _ tm) = checkAllNameBounded ctx tm
checkAllNameBounded ctx (TmLetIn name ty tm bdy) =
  combineNameBoundStatus
    [ checkAllNameBounded ctx ty,
      checkAllNameBounded ctx tm,
      checkAllNameBounded (addName ctx name) bdy ]
checkAllNameBounded ctx (TmIndType name tmlst) =
  combineNameBoundStatus
    ( (if isNameBound ctx name then AllNameBounded else UnboundNameInTerm [name]) :
      map (checkAllNameBounded ctx) tmlst)
checkAllNameBounded ctx (TmConstr name tmlst) =
  combineNameBoundStatus
    ( (if isNameBound ctx name then AllNameBounded else UnboundNameInTerm [name]) :
      map (checkAllNameBounded ctx) tmlst)
checkAllNameBounded _ TmType = AllNameBounded
checkAllNameBounded _ TmTypeHigher = 
  error "This should not happen: checkAllNameBounded TmTypeHigher"
checkAllNameBounded ctx tmmatch@(TmMatch n tm name namelst rty equlst) =
  combineNameBoundStatus
    [ checkMatchIndType ctx tmmatch
    , checkMatchConstrEqulst ctx tmmatch
    , checkMatchBound ctx tmmatch ]

checkMatchIndType :: Context -> Term -> NameBoundStatus
checkMatchIndType ctx tmmatch@(TmMatch _ tm name namelst rty equlst) =
  case namelst of
    [] -> NoIndTypeProvided tmmatch
    (i:is) -> case getIndType ctx i of
      Left err -> UnknownIndType tmmatch i
      Right (n, ty, _, constrlst) -> let numOfTypeParams = countParams ty in
        if numOfTypeParams /= length (tail namelst)
          then WrongNumParamsInTypeMatching tmmatch namelst
          else case checkNameLst n (tail namelst) of
            nlst@(x:xs) -> UnusedNameInTypeMatching tmmatch [namelst !! t | t <- nlst]
            [] ->
              let
                groupedNameLst = group $ sort (tail namelst)
                duplicateNameLst = map head . filter (\x -> length x >= 2) $ groupedNameLst
                duplicateNameLstNoUL =
                  case duplicateNameLst of
                    [] -> []
                    (x:xs) -> if x == "_" then xs else duplicateNameLst
              in
                if not $ null duplicateNameLstNoUL
                  then DuplicateNameInTypeMatching tmmatch duplicateNameLstNoUL
                  else AllNameBounded

checkMatchConstrEqulst :: Context -> Term -> NameBoundStatus
checkMatchConstrEqulst ctx tmmatch@(TmMatch _ tm name namelst rty equlst) =
  case getIndType ctx (head namelst) of
    Right (n, _, _, constrlst) ->
      let
        equConstrNameLst = sort $ map (\case Equation namelst _ -> head namelst) equlst
        constrNameLst = sort $ map (\case Constructor namec _ _ -> namec) constrlst
        groupedNameLst = group equConstrNameLst
        duplicateNameLst = map head . filter (\x -> length x >= 2) $ groupedNameLst
        noDuplicateNameLst = map head groupedNameLst
        unboundNameLst = noDuplicateNameLst \\ constrNameLst
        notOccuredNameLst = constrNameLst \\ noDuplicateNameLst
      in
        if not $ null duplicateNameLst
          then DuplicateConstr tmmatch duplicateNameLst
          else if not $ null unboundNameLst
            then UnknownConstr tmmatch unboundNameLst
            else if not $ null notOccuredNameLst
              then InsufficientConstrs tmmatch notOccuredNameLst
              else
                let
                  cmpForEqu :: Equation -> Equation -> Ordering
                  cmpForEqu (Equation namelst1 _) (Equation namelst2 _) =
                    compare namelst1 namelst2
                  cmpForConstr :: Constructor -> Constructor -> Ordering
                  cmpForConstr (Constructor name1 _ _) (Constructor name2 _ _) =
                    compare name1 name2
                in
                  combineNameBoundStatus $
                    zipWith
                    ( checkMatchConstrEqu ctx n tmmatch )
                    ( sortBy cmpForEqu equlst )
                    ( sortBy cmpForConstr constrlst )

checkMatchConstrEqu :: Context -> Int -> Term -> Equation -> Constructor -> NameBoundStatus
checkMatchConstrEqu ctx n tmmatch (Equation namelst tm) (Constructor name tyc tmc) =
  if countParams tyc /= length namelst - 1
    then WrongNumParamsInConstrMatching tmmatch namelst
    else case checkNameLst n (tail namelst) of
      nlst@(x:xs) -> UnusedNameInConstrMatching tmmatch namelst [namelst !! t | t <- nlst]
      [] ->
        let
          groupedNameLst = group $ sort (tail namelst)
          duplicateNameLst = map head . filter (\x -> length x >= 2) $ groupedNameLst
          duplicateNameLstNoUL =
            case duplicateNameLst of
              [] -> []
              (x:xs) -> if x == "_" then xs else duplicateNameLst
        in
          if not $ null duplicateNameLstNoUL
            then DuplicateNameInConstrMatching tmmatch namelst duplicateNameLstNoUL
            else AllNameBounded

checkMatchBound :: Context -> Term -> NameBoundStatus
checkMatchBound ctx tmmatch@(TmMatch _ tm name namelst rty equlst) =
  case getIndType ctx (head namelst) of
    Right (n, _, _, constrlst) ->
      combineNameBoundStatus
      ( checkAllNameBounded ctx tm :
        checkAllNameBounded
          (addName (foldl addName ctx (drop (n + 1) namelst)) name) rty :
        map (checkAllNameBoundedEqu ctx n) equlst)

checkAllNameBoundedEqu :: Context -> Int -> Equation -> NameBoundStatus
checkAllNameBoundedEqu ctx n (Equation namelst tm) =
  checkAllNameBounded (foldl addName ctx (drop (n + 1) namelst)) tm

checkAllNameBoundedCommand :: Context -> Command -> NameBoundStatus
checkAllNameBoundedCommand ctx (Ax _ tm) = checkAllNameBounded ctx tm
checkAllNameBoundedCommand ctx (Def _ ty tm) = 
  combineNameBoundStatus
    [ checkAllNameBounded ctx ty, checkAllNameBounded ctx tm]
checkAllNameBoundedCommand ctx (Ind name _ ty tm constrlst) =
  let
    ctxWithName = addName ctx name
  in
    combineNameBoundStatus
      ( checkAllNameBounded ctxWithName ty :
        checkAllNameBounded ctxWithName tm :
        concatMap (\(namec,tyc,tmc) ->
          [ checkAllNameBounded (addName ctxWithName namec) tyc
          , checkAllNameBounded (addName ctxWithName namec) tmc ])
        constrlst )
checkAllNameBoundedCommand ctx (Fix _ tm) = checkAllNameBounded ctx tm

