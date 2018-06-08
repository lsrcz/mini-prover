module MiniProver.Proof.HandleTactic (
    handleTactic
  ) where

import MiniProver.Core.Syntax
import MiniProver.Proof.ProofDef
import MiniProver.Proof.Tactics.Exact (handleExact)
import MiniProver.Proof.Tactics.Intro (handleIntro)
import MiniProver.Proof.Tactics.Intros (handleIntros)

handleTactic :: Goal -> Tactic -> Either TacticError Result
handleTactic g@Goal{} e@Exact{} = handleExact g e
handleTactic g@Goal{} i@Intro{} = handleIntro g i
handleTactic g@Goal{} i@Intros{} = handleIntros g i
