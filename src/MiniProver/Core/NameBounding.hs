{-# LANGUAGE LambdaCase #-}
module MiniProver.Core.NameBounding (
    NameBoundStatus(..)
  , checkAllNameBounded
  , checkAllNameBoundedCommand
  ) where

import MiniProver.Core.Syntax
import MiniProver.Core.Context
import Data.List (group, sort, concatMap, find, (\\), sortBy)
import Data.Maybe (fromMaybe)

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

unique :: (Eq a) => [a] -> [a]
unique = map head . group

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

