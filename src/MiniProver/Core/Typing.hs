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

typeof :: Context -> Term -> Either TypingError Term
typeof = undefined
