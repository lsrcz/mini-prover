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
         (nm, ty, _) -> 
            posCheck ctx name ty []) conlst)

eqlistStripMatch :: [Equation] -> [Equation] -> Bool
eqlistStripMatch lst1 lst2 =
    case lst1 of
        [] -> lst2 == []
        (Equation namelst t1):b -> 
            case lst2 of
                [] -> False
                (Equation namelst1 t2):d -> 
                    (namelst == namelst1) &&
                    (stripMatch (t1, t2)) &&    
                    (eqlistStripMatch b d)


listStripMatch :: [Term] -> [Term] -> Bool
listStripMatch lst1 lst2 =
    case lst1 of
        [] -> lst2 == []
        a:b -> 
            case lst2 of
                [] -> False
                c:d -> 
                    (stripMatch (a, c)) && 
                    (listStripMatch b d)

stripMatch :: (Term, Term) -> Bool
stripMatch pairterm =
    case pairterm of
        (TmRel name _, TmRel name1 _) -> 
            (name == name1)
        (TmVar name, TmVar name1) -> 
            (name == name1)
        (TmAppl lst1, TmAppl lst2) -> 
            listStripMatch lst1 lst2
        (TmProd name t1 tt1, TmProd name1 t2 tt2) -> 
            (name == name1) &&
            (stripMatch (t1, t2)) && 
            (stripMatch (tt1, tt2))
        (TmLambda name t1 tt1, TmLambda name1 t2 tt2) ->
            (name == name1) &&
            (stripMatch (t1, t2)) && (stripMatch (tt1, tt2))
        (TmFix _ t1, TmFix _ t2) -> 
            stripMatch (t1, t2)
        (TmLetIn name t1 tt1 ttt1, TmLetIn name1 t2 tt2 ttt2) ->
            (name == name1) &&
            (stripMatch (t1, t2)) && 
            (stripMatch (tt1, tt2)) && 
            (stripMatch (ttt1, ttt2))
        (TmIndType name lst1, TmIndType name1 lst2) ->
            (name == name1) &&
            (listStripMatch lst1 lst2)
        (TmConstr name lst1, TmConstr name1 lst2) ->
            (name == name1) &&
            (listStripMatch lst1 lst2)
        (TmType, TmType) -> True
        (TmTypeHigher, TmTypeHigher) -> True
        (TmMatch _ t1 name namelist tt1 eqlst1, 
            TmMatch _ t2 name1 namelist1 tt2 eqlst2) ->
                (name == name1) && 
                (namelist == namelist1) &&
                (stripMatch (t1, t2)) && 
                (stripMatch (tt1, tt2)) && 
                (eqlistStripMatch eqlst1 eqlst2)
        _ -> False

nestPosCheck :: Context -> Name -> Term -> [Term] -> Bool
nestPosCheck ctx name term nestchecked
    | any (\x -> stripMatch (x, term)) nestchecked = True
    | otherwise =
        let newchecked = term:nestchecked in
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
                (strictPosCheck ctx name tm1 newchecked) &&
                (nestPosCheck ctx name tm2 newchecked) 
              _-> False

instantiate :: Context -> [Term] -> Term -> Term
instantiate ctx tmlst term =
    fullBReduction ctx (TmAppl (term:tmlst))

strictPosCheck :: Context -> Name -> Term -> [Term] -> Bool
strictPosCheck ctx name term nestchecked
    | dontOccur name term = True
    | otherwise =
        case fullBZIReduction ctx term of 
          TmProd _ tm1 tm2 ->
            (dontOccur name tm1) &&
            (strictPosCheck ctx name tm2 nestchecked)
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
                                let newty = instantiate ctx alst ty in
                                    nestPosCheck ctx name newty nestchecked
                                ) conlst) 
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
      TmMatch _ tm1 _ _ tm2 eqlst ->
        (dontOccurFree name tm1) && 
        (dontOccurFree name tm2) && 
        (all (\case 
             (Equation _ tm) -> 
                dontOccurFree name tm) eqlst)
      _ -> True

posCheck :: Context -> Name -> Term -> [Term] -> Bool
posCheck ctx name term nestchecked = 
    case term of 
      TmIndType nm tmlst ->
        (nm == name) &&
        (all (\x -> dontOccurFree name x) tmlst)
      TmProd nm tm1 tm2 ->
        (strictPosCheck ctx name tm1 nestchecked) &&
        (posCheck ctx name tm2 nestchecked)
      _ -> False

arityCheck :: Term -> Bool
arityCheck term =
    case term of
      TmProd _ _ tm -> arityCheck tm
      TmType -> True
      _ -> False

