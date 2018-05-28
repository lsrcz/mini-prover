module MiniProver.Core.Rename (
    renameInd
  ) where

import MiniProver.Core.Syntax
import MiniProver.Core.Context
import Data.Char (toLower)
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

renameTerm :: Context -> Term -> Term
renameTerm ctx tm@(TmRel name idx)
  | head name == '.' =
      TmRel (fromRight (error "This should not happen") (indexToName ctx idx)) idx
  | otherwise = tm
renameTerm ctx (TmAppl tmlst) =
  TmAppl $ map (renameTerm ctx) tmlst
renameTerm ctx (TmProd name ty tm)
  | head name == '.' =
      let
        origname = getOrigNameFromTy ty
        (newctx,newname) = pickFreshName ctx origname
      in
        TmProd newname (renameTerm ctx ty) (renameTerm newctx tm)
  | otherwise = TmProd name (renameTerm ctx ty) (renameTerm (addName ctx name) tm)
renameTerm ctx (TmLambda name ty tm)
  | head name == '.' =
      let
        origname = getOrigNameFromTy ty
        (newctx,newname) = pickFreshName ctx origname
      in
        TmLambda newname (renameTerm ctx ty) (renameTerm newctx tm)
  | otherwise = TmLambda name (renameTerm ctx ty) (renameTerm (addName ctx name) tm)
renameTerm ctx (TmFix i tm) = TmFix i (renameTerm ctx tm)
renameTerm ctx (TmLetIn name ty tm bdy)
  | head name == '.' =
      let
        origname = getOrigNameFromTy ty
        (newctx,newname) = pickFreshName ctx origname
      in
        TmLetIn newname (renameTerm ctx ty) (renameTerm ctx tm) (renameTerm newctx bdy)
  | otherwise =
      TmLetIn name
        (renameTerm ctx ty)
        (renameTerm ctx tm)
        (renameTerm (addName ctx name) bdy)
renameTerm ctx (TmIndType name tmlst) = TmIndType name $ map (renameTerm ctx) tmlst
renameTerm ctx (TmConstr name tmlst) = TmConstr name $ map (renameTerm ctx) tmlst
renameTerm ctx (TmMatch i tm name namelst retty equlst) =
  TmMatch i (renameTerm ctx tm) name namelst
  (renameTerm (addName (foldl addName ctx (drop (i + 1) namelst)) name) retty)
  (map (renameEqu i ctx) equlst)
renameTerm _ tm = tm

renameEqu :: Int -> Context -> Equation -> Equation
renameEqu i ctx (Equation namelst tm) =
  Equation namelst (renameTerm (foldl addName ctx (drop (i + 1) namelst)) tm)
