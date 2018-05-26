module MiniProver.Core.Subst (
    tmShiftAbove
  , tmShift
  , tmSubst
  , tmSubstTop
  , tmSubstInsideN
  , bindingShift
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
      TmFix n tm -> TmFix n (walk c' tm)
      TmLetIn name ty tm bdy -> TmLetIn name (walk c' ty) (walk c' tm) (walk (c' + 1) bdy)
      TmIndType name lst -> TmIndType name $ map (walk c') lst
      TmConstr name lst -> TmConstr name $ map (walk c') lst
      TmMatch n tm name namelst rty equlst ->
        if n == (-1)
          then error "This should not happen"
          else TmMatch n (walk c' tm) name namelst (walk (c' + length namelst - 1 - n) rty) (map (walkequ n c') equlst)
      _ -> t'
    walkequ :: Int -> Int -> Equation -> Equation
    walkequ n c' e' = case e' of
      Equation namelst tm -> Equation namelst (walk (c' + length namelst - 1 - n) tm)
  in
    walk c t

tmShiftAbove :: Int -> Int -> Term -> Term
tmShiftAbove d =
  tmMap
  (\n c x -> if x >= c then TmRel n (x + d) else TmRel n x)

tmShift :: Int -> Term -> Term
tmShift d = tmShiftAbove d 0

bindingShift :: Int -> Binding -> Binding
bindingShift d NameBind = NameBind
bindingShift d (IndTypeBind i ty tm constrlst) = 
  IndTypeBind i ty tm constrlst
bindingShift d (VarBind tm) = VarBind (tmShift d tm)
bindingShift d (TmAbbBind ty tm) = TmAbbBind (tmShift d ty) (tmShift d <$> tm)

tmSubst :: Index -> Term -> Term -> Term
tmSubst j s =
  tmMap
  (\n j' x -> if x == j' then tmShift j' s else TmRel n x)
  j

tmSubstTop :: Term -> Term -> Term
tmSubstTop s t =
  tmShift (-1) (tmSubst 0 (tmShift 1 s) t)

-- tmSubstTop is tmSubstInsideN 1
tmSubstInsideN :: Int -> Term -> Term -> Term
tmSubstInsideN n s t =
  tmShiftAbove (-1) (n - 1) (tmSubst (n - 1) (tmShift 1 s) t)
