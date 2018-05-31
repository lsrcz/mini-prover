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

addAnonymousName :: Context -> [Name] -> Name -> Maybe Term -> (Context, Name)
addAnonymousName ctx lst name mty
  | head name == '.' =
      let
        origname =
          if length name == 1 || isDigit (name !! 1)
            then case mty of
              Nothing -> "a"
              Just ty -> getOrigNameFromTy ty
            else [name !! 1]
      in
        pickFreshNameWithRejectList ctx lst origname
  | otherwise = (addName ctx name, name)

renameTerm :: Context -> Term -> Term
renameTerm = renameTerm' []

renameTerm' :: [Name] -> Context -> Term -> Term
renameTerm' _ ctx tm@(TmRel name idx)
  | head name == '.' =
      TmRel (fromRight (error "This should not happen") (indexToName ctx idx)) idx
  | otherwise = tm
renameTerm' lst ctx (TmAppl tmlst) =
  TmAppl $ map (renameTerm' lst ctx) tmlst
renameTerm' lst ctx (TmProd name ty tm) =
  let
    (newctx,newname) = addAnonymousName ctx lst name (Just ty)
  in
    TmProd newname (renameTerm' (newname:lst) ctx ty) (renameTerm' lst newctx tm)
renameTerm' lst ctx (TmLambda name ty tm) =
  let
    (newctx,newname) = addAnonymousName ctx lst name (Just ty)
  in
    TmLambda newname (renameTerm' (newname:lst) ctx ty) (renameTerm' lst newctx tm)
renameTerm' lst ctx (TmFix i tm) = TmFix i (renameTerm' lst ctx tm)
renameTerm' lst ctx (TmLetIn name ty tm bdy) =
  let
    (newctx,newname) = addAnonymousName ctx lst name (Just ty)
  in
    TmLetIn newname (renameTerm' (newname:lst) ctx ty) (renameTerm' (newname:lst) ctx tm) (renameTerm' lst newctx bdy)
renameTerm' lst ctx (TmIndType name tmlst) = TmIndType name $ map (renameTerm' lst ctx) tmlst
renameTerm' lst ctx (TmConstr name tmlst) = TmConstr name $ map (renameTerm' lst ctx) tmlst
renameTerm' lst ctx (TmMatch i tm name namelst retty equlst) =
  let
    (newctx,newNameLst) = foldl (addWithNameList lst) (ctx,[]) (drop (i + 1) namelst)
    (newctx1,newName) = addAnonymousName newctx lst ['.',head $ head namelst] Nothing
  in
    TmMatch i (renameTerm' lst ctx tm) newName (take (i + 1) namelst ++ newNameLst)
    (renameTerm' lst newctx1 retty)
    (map (renameEqu lst i ctx) equlst)
renameTerm' _ _ tm = tm

addWithNameList :: [Name] -> (Context, [Name]) -> Name -> (Context, [Name])
addWithNameList rejlst (ctx, lst) nameToAdd =
  case addAnonymousName ctx rejlst nameToAdd Nothing of
    (newctx,newname) -> (newctx,lst ++ [newname])

renameEqu :: [Name] -> Int -> Context -> Equation -> Equation
renameEqu lst i ctx (Equation namelst tm) =
  let
    (newctx,newNameLst) = foldl (addWithNameList lst) (ctx,[]) (drop (i + 1) namelst)
  in
    Equation (take (i + 1) namelst ++ newNameLst) (renameTerm' lst newctx tm)
