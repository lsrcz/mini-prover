module MiniProver.Core.Rename (
    renameInd
  , getOrigNameFromTy
  , renameTerm
  ) where

import MiniProver.Core.Syntax
import MiniProver.Core.Context
import Data.Char (toLower, isDigit)
import Data.Either (fromRight)

renameInd :: Context -> Command -> Command
renameInd ctx (Ind name i ty tm constrlst) =
  Ind name i (renameTerm ctx ty) (renameTerm ctx tm)
  (map (\(namec,tyc,tmc) -> (namec, renameTerm ctx tyc, renameTerm ctx tmc)) constrlst)

getOrigNameFromTy :: Term -> String
getOrigNameFromTy (TmRel name _) = [toLower $ head name]
getOrigNameFromTy (TmAppl _) = "f"
getOrigNameFromTy (TmProd _ _ tm) = getOrigNameFromTyIn tm
getOrigNameFromTy (TmLetIn _ _ _ bdy) = getOrigNameFromTyIn bdy
getOrigNameFromTy (TmIndType name _) = [toLower $ head name]
getOrigNameFromTy (TmConstr name _) = [toLower $ head name]
getOrigNameFromTy _ = "a"

getOrigNameFromTyIn :: Term -> String
getOrigNameFromTyIn (TmProd _ _ tm) = getOrigNameFromTyIn tm
getOrigNameFromTyIn TmType = "P"
getOrigNameFromTyIn _ = "f"

addAnonymousName :: Context -> Name -> Maybe Term -> (Context, Name)
addAnonymousName ctx name mty
  | head name == '.' =
      let
        origname =
          if length name == 1 || isDigit (name !! 1)
            then case mty of
              Nothing -> "a"
              Just ty -> getOrigNameFromTy ty
            else [name !! 1]
      in
        pickFreshName ctx origname
  | otherwise = (addName ctx name, name)

renameTerm :: Context -> Term -> Term
renameTerm ctx tm@(TmRel name idx)
  | head name == '.' =
      TmRel (fromRight (error "This should not happen") (indexToName ctx idx)) idx
  | otherwise = tm
renameTerm ctx (TmAppl tmlst) =
  TmAppl $ map (renameTerm ctx) tmlst
renameTerm ctx (TmProd name ty tm) =
  let
    (newctx,newname) = addAnonymousName ctx name (Just ty)
  in
    TmProd newname (renameTerm ctx ty) (renameTerm newctx tm)
renameTerm ctx (TmLambda name ty tm) =
  let
    (newctx,newname) = addAnonymousName ctx name (Just ty)
  in
    TmLambda newname (renameTerm ctx ty) (renameTerm newctx tm)
renameTerm ctx (TmFix i tm) = TmFix i (renameTerm ctx tm)
renameTerm ctx (TmLetIn name ty tm bdy) =
  let
    (newctx,newname) = addAnonymousName ctx name (Just ty)
  in
    TmLetIn newname (renameTerm ctx ty) (renameTerm ctx tm) (renameTerm newctx bdy)
renameTerm ctx (TmIndType name tmlst) = TmIndType name $ map (renameTerm ctx) tmlst
renameTerm ctx (TmConstr name tmlst) = TmConstr name $ map (renameTerm ctx) tmlst
renameTerm ctx (TmMatch i tm name namelst retty equlst) =
  let
    (newctx,newNameLst) = foldl addWithNameList (ctx,[]) (drop (i + 1) namelst)
    (newctx1,newName) = addAnonymousName newctx ['.',head $ head namelst] Nothing
  in
    TmMatch i (renameTerm ctx tm) newName (take (i + 1) namelst ++ newNameLst)
    (renameTerm newctx1 retty)
    (map (renameEqu i ctx) equlst)
renameTerm _ tm = tm

addWithNameList :: (Context, [Name]) -> Name -> (Context, [Name])
addWithNameList (ctx, lst) nameToAdd =
  case addAnonymousName ctx nameToAdd Nothing of
    (newctx,newname) -> (newctx,lst ++ [newname])

renameEqu :: Int -> Context -> Equation -> Equation
renameEqu i ctx (Equation namelst tm) =
  let
    (newctx,newNameLst) = foldl addWithNameList (ctx,[]) (drop (i + 1) namelst)
  in
    Equation (take (i + 1) namelst ++ newNameLst) (renameTerm newctx tm)
