module MiniProver.Core.Typing (
    simplifyType
  , typeof
  ) where

import MiniProver.Core.Syntax
import MiniProver.Core.Subst
import MiniProver.Core.Context
import MiniProver.TopLevel.PrettyPrint

data TypingError = 
    TypingError Term String
  deriving (Eq, Show)

-- Trying to simplify the type to a still readable term
-- only do beta-reduction in certain cases
-- should only apply to well-typed term, applying to ill-typed term is undefined
-- no context needed
simplifyType :: Term -> Term
simplifyType (TmAppl lst) =
  case map simplifyType lst of
    [x] -> x
    (x:y:xs) ->
      case x of
        TmLambda _ _ tm -> simplifyType $ TmAppl $ tmSubstTop y tm : xs
        _ -> TmAppl (x:y:xs)
    _ -> error "This should not happen"
simplifyType (TmProd name ty tm) =
  TmProd name (simplifyType ty) (simplifyType tm)
simplifyType tm = tm

typeof :: Context -> Term -> Either TypingError Term -- type
typeof = undefined
