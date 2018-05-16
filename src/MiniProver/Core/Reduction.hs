module MiniProver.Core.Reduction (
    betaReduction
  , zetaReduction
  , iotaReduction
  , deltaReduction
  , etaExpansion
  ) where

import MiniProver.Core.Syntax
import MiniProver.Core.Subst
import MiniProver.Core.Context

-- not context sensitive
betaReduction :: Term -> Term
betaReduction (TmAppl [TmLambda _ _ tm, tm1]) =
  tmSubstTop tm1 tm
betaReduction (TmAppl (TmLambda _ _ tm:tm1:xs)) =
  TmAppl $ tmSubstTop tm1 tm : xs
betaReduction (TmAppl [TmProd _ _ tm, tm1]) =
  tmSubstTop tm1 tm
betaReduction (TmAppl (TmProd _ _ tm:tm1:xs)) =
  TmAppl $ tmSubstTop tm1 tm : xs
betaReduction (TmAppl (TmFix tm:tm1:xs)) =
  betaReduction $ betaReduction (TmAppl (tm:TmFix tm:tm1:xs))
betaReduction _ = error "beta reduction can only be applied to application"

zetaReduction :: Term -> Term
zetaReduction (TmLetIn _ _ tm bdy) =
  tmSubstTop tm bdy
zetaReduction _ = error "zeta reduction can only be applied to local definition(letin)"

iotaReduction :: Term -> Term
iotaReduction (TmMatch (TmConstr name lst) _ _ equlist) = go equlist
  where
    go :: [Equation] -> Term
    go [] = error "Pattern matching shouldn't fail in well-typed term"
    go (x:xs) =
      case x of
        Equation names tm ->
          if name == head names
            then
              snd $ foldl (\(n,acc) tm1 -> (n - 1, tmSubstInsideN n tm1 acc))
                (length lst, tm) lst
            else go xs

deltaReduction :: Context -> Term -> Term
deltaReduction ctx (TmRel _ idx) =
  case getBinding ctx idx of
    Right (TmAbbBind _ (Just tm)) -> tm
    Right (TmAbbBind _ Nothing) -> error "delta reduction can not be applied to axioms"
    Left _ -> error "This should not happen in well-typed term"
    _ -> error "delta reduction can only be applied to definitions"
deltaReduction _ _ = error "delta reduction can only be applied to variables"

-- tm : forall x:ity, ty2
etaExpansion :: Term -> Name -> Term -> Term
etaExpansion tm iname ity = TmLambda iname ity (TmAppl [tmShift 1 tm, TmRel iname 0])
