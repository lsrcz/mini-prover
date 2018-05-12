module MiniProver.Core.Typing (
    typeof
  ) where

import MiniProver.Core.Syntax
import MiniProver.Core.Subst
import MiniProver.Core.Context

data TypingError = 
    SimpleError Term String
  | ExpectedTypeNotMatch Term Term String
  deriving (Eq, Show)

-- Trying to simplify the type to a still readable term
-- only do beta-reduction in certain cases
simplifyType :: Context -> Term -> Term
simplifyType ctx (TmAppl lst) =
  case map (simplifyType ctx) lst of
    [x] -> x
    (x:y:xs) ->
      case x of
        TmLambda _ _ tm -> simplifyType ctx $ TmAppl $ tmSubstTop y tm : xs
        _ -> TmAppl (x:y:xs)
    _ -> error "This should not happen"

typeof :: Context -> Term -> Either TypingError Term -- type
typeof = undefined
