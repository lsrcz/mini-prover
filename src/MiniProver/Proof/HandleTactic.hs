module MiniProver.Proof.HandleTactic (
    handleTactic
  ) where

import MiniProver.Core.Syntax
import MiniProver.Proof.ProofDef
import MiniProver.Proof.Tactics.Exact (handleExact)

handleTactic :: Goal -> Tactic -> Either TacticError Result
handleTactic g@Goal{} e@Exact{} = handleExact g e