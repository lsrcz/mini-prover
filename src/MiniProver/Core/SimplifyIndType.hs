module MiniProver.Core.SimplifyIndType (
    simplifyIndType
  ) where

import MiniProver.Core.Syntax
import MiniProver.Core.Context
import MiniProver.Core.Reduction

simplToConstrOrIndType :: Term -> Bool
simplToConstrOrIndType (TmIndType _ _) = True
simplToConstrOrIndType (TmConstr _ _) = True
simplToConstrOrIndType (TmProd _ _ tm) = simplToConstrOrIndType tm
simplToConstrOrIndType (TmLambda _ _ tm) = simplToConstrOrIndType tm
simplToConstrOrIndType _ = False

reductionToNotAnAppl :: Term -> Term
reductionToNotAnAppl tm@(TmAppl [_,_]) = betaReduction tm
reductionToNotAnAppl tm@(TmAppl (_:_)) = reductionToNotAnAppl $ betaReduction tm

simplifyIndType :: Term -> Term
simplifyIndType tm@(TmAppl lst@(x:_))
  | simplToConstrOrIndType x = simplifyIndType $ reductionToNotAnAppl tm
  | otherwise = TmAppl (map simplifyIndType lst)
simplifyIndType (TmProd name ty tm) = 
  TmProd name (simplifyIndType ty) (simplifyIndType tm)
simplifyIndType (TmLambda name ty tm) = 
  TmLambda name (simplifyIndType ty) (simplifyIndType tm)
simplifyIndType (TmFix i tm) = TmFix i $ simplifyIndType tm
simplifyIndType (TmLetIn name ty tm bdy) =
  TmLetIn name (simplifyIndType ty) (simplifyIndType tm) (simplifyIndType bdy)
simplifyIndType (TmIndType name tmlst) =
  TmIndType name (map simplifyIndType tmlst)
simplifyIndType (TmConstr name tmlst) =
  TmConstr name (map simplifyIndType tmlst)
simplifyIndType (TmMatch i tm name namelst retty equlst) =
  TmMatch i (simplifyIndType tm) name namelst (simplifyIndType retty)
  (map simplifyIndTypeEqu equlst)
simplifyIndType tm = tm

simplifyIndTypeEqu :: Equation -> Equation
simplifyIndTypeEqu (Equation namelst tm) = Equation namelst (simplifyIndType tm)