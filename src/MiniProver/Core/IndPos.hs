{-# LANGUAGE LambdaCase #-}
module MiniProver.Core.IndPos (
    isPositive
  ) where

import MiniProver.Core.Syntax
import MiniProver.Core.Context
import MiniProver.Core.Reduction
import Data.Either (fromRight)

isPositive :: Context -> Command -> Bool
isPositive ctx (Ind name d term1 term2 conlst) =
    (arityCheck term1) && 
    (all (\case 
         (nm, tm1, tm2) -> 
            posCheck ctx name tm1) conlst)

nestPosCheck :: Context -> Name -> Term -> Bool
nestPosCheck ctx name term =
    case term of
      TmIndType nm tmlst ->
        (nm /= name) &&
        let 
            (d, _, _, _) = 
                fromRight (error "This should not happen") 
                    (getIndType ctx nm) 
        in
            let (_, ulst) = seperateIndTerm d tmlst in
                all (\x -> dontOccur name x) ulst
      TmProd _ tm1 tm2 -> 
        (strictPosCheck ctx name tm1) &&
        (nestPosCheck ctx name tm2) 
      _-> False

instantiate :: [Term] -> Term -> Term
instantiate tmlst term =
    case tmlst of 
        [] -> term
        a:b -> instantiate b $ betaReduction $ TmAppl [term, a]

strictPosCheck :: Context -> Name -> Term -> Bool
strictPosCheck ctx name term 
    | dontOccur name term = True
    | otherwise =
        case term of 
          TmProd _ tm1 tm2 ->
            (dontOccur name tm1) &&
            (strictPosCheck ctx name tm2)
          TmIndType nm tmlst 
            | nm == name -> 
              all (\x -> dontOccurFree name x) tmlst
            | otherwise ->
                let 
                    (d, _, _, conlst) = 
                        fromRight (error "This should not happen") 
                            (getIndType ctx nm) 
                in
                    let (alst, tlst) = seperateIndTerm d tmlst in
                        (all (\x -> dontOccur name x) tlst) &&
                        (all (\case 
                             (Constructor _ ty _) -> 
                                nestPosCheck ctx name 
                                    (instantiate alst ty)) conlst) 
          _ -> False

seperateIndTerm :: Int -> [Term] -> ([Term], [Term])
seperateIndTerm d tmlst =
    if d == 0 then ([], tmlst)
        else let 
                (a, b) = seperateIndTerm (d - 1) $ tail tmlst
             in
                ((head tmlst):a, b)

dontOccur :: Name -> Term -> Bool
dontOccur = dontOccurFree

dontOccurFree :: Name -> Term -> Bool
dontOccurFree name term =
    case term of
      TmAppl tmlst -> 
        all (\x -> dontOccurFree name x) tmlst
      TmProd _ tm1 tm2 ->
        (dontOccurFree name tm1) && 
        (dontOccurFree name tm2)
      TmLambda _ tm1 tm2 -> 
        (dontOccurFree name tm1) && 
        (dontOccurFree name tm2)
      TmFix _ tm -> 
        dontOccurFree name tm
      TmLetIn _ tm1 tm2 tm3 ->
        (dontOccurFree name tm1) && 
        (dontOccurFree name tm2) && 
        (dontOccurFree name tm3)
      TmIndType nm tmlst -> 
        (nm /= name) && 
        (all (\x -> dontOccurFree name x) tmlst)
      TmConstr nm tmlst ->
        all (\x -> dontOccurFree name x) tmlst
      TmMatch tm1 _ tm2 eqlst ->
        (dontOccurFree name tm1) && 
        (dontOccurFree name tm2) && 
        (all (\case 
             (Equation _ tm) -> 
                dontOccurFree name tm) eqlst)
      _ -> True

posCheck :: Context -> Name -> Term -> Bool
posCheck ctx name term = 
    case term of 
      TmIndType nm tmlst ->
        (nm == name) &&
        (all (\x -> dontOccurFree name x) tmlst)
      TmProd nm tm1 tm2 ->
        (strictPosCheck ctx name tm1) &&
        (posCheck ctx name tm2)
      _ -> False

arityCheck :: Term -> Bool
arityCheck term =
    case term of
      TmProd _ _ tm -> arityCheck tm
      TmType -> True
      _ -> False

