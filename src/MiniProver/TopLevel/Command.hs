module MiniProver.TopLevel.Command where

import MiniProver.Core.Syntax
import MiniProver.Core.Context
import MiniProver.Core.Typing (TypingError)

typeof :: Context -> Term -> Either TypingError Term
typeof _ _ = Right TmType

addEnvCommand :: Context -> Command -> Context
addEnvCommand _ _ = undefined