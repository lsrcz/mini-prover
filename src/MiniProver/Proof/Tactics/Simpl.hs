{-# LANGUAGE LambdaCase #-}
module MiniProver.Proof.Tactics.Simpl (
    handleSimpl
  ) where

import MiniProver.Proof.ProofDef
import MiniProver.Core.Context
import MiniProver.Core.Syntax
import MiniProver.Core.Reduction
import MiniProver.Core.Subst
import MiniProver.Core.Rename

handleSimpl :: Goal -> Tactic -> Either TacticError Result
handleSimpl g@(Goal d ctx ty) s@(Simpl Nothing) =
  Right $ Result
  [ Goal d ctx
    ( reductionWithStrategy
      ( clearStrategyInSet (clearStrategyInSet fullBZIDStrategySet DeltaRestricted) DeltaRel)
      ctx ty)]
  (\[tm] -> tm)

