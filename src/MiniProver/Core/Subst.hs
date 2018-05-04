module MiniProver.Core.Subst (
    tmShiftAbove
  , tmShift
  , tmSubstTop
  ) where

import MiniProver.Core.Syntax

-- shifting
tmMap :: (Name -> Index -> Index -> Term) -> Int -> Term -> Term
tmMap onRel c t =
  let
    walk :: Int -> Term -> Term
    walk c' t' = case t' of
      TmRel n i -> onRel n c' i
      TmAppl lst -> TmAppl $ map (walk c') lst
      TmProd name ty tm -> TmProd name (walk c' ty) (walk (c' + 1) tm)
      TmLambda name ty tm -> TmLambda name (walk c' ty) (walk (c' + 1) tm)
      TmFix tm -> TmFix (walk c' tm)
      TmLetIn name ty tm bdy -> TmLetIn name (walk c' ty) (walk c' tm) (walk (c' + 1) bdy)
      TmIndType name lst -> TmIndType name $ map (walk c') lst
      TmMatch tm namelst rty equlst -> 
        TmMatch (walk c' tm) namelst (walk (c' + length namelst - 1) rty) (map (walkequ c') equlst)
      _ -> t'
    walkequ :: Int -> Equation -> Equation
    walkequ c' e' = case e' of
      Equation namelst tm -> Equation namelst (walk (c' + length namelst - 1) tm)
  in
    walk c t

tmShiftAbove :: Int -> Int -> Term -> Term
tmShiftAbove d =
  tmMap
  (\n c x -> if x >= c then TmRel n (x + d) else TmRel n x)

tmShift :: Int -> Term -> Term
tmShift d = tmShiftAbove d 0

tmSubst :: Index -> Term -> Term -> Term
tmSubst j s =
  tmMap
  (\n j' x -> if x == j' then tmShift j' s else TmRel n x)
  j

tmSubstTop :: Term -> Term -> Term
tmSubstTop s t =
  tmShift (-1) (tmSubst 0 (tmShift 1 s) t)