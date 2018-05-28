{-# LANGUAGE LambdaCase #-}
module MiniProver.TopLevel.Command (
    addEnvCommand
  ) where

import MiniProver.Core.Syntax
import MiniProver.Core.Context

addEnvCommand :: Context -> Command -> Context
addEnvCommand ctx (Ax nm ty) = 
    addBinding ctx nm (TmAbbBind ty Nothing)
addEnvCommand ctx (Def nm ty tm) = 
    addBinding ctx nm (TmAbbBind ty (Just tm))
addEnvCommand ctx (Fix nm tm) = 
    case tm of 
      TmFix _ (TmLambda _ ty _) -> 
        addBinding ctx nm (TmAbbBind ty (Just tm))
      _ -> error "This should not happen"
addEnvCommand ctx (Ind nm d ty tm eqlst) = undefined
