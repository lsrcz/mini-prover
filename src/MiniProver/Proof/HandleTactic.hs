module MiniProver.Proof.HandleTactic (
    handleTactic
  ) where

import MiniProver.Core.Syntax
import MiniProver.Proof.ProofDef
import MiniProver.Proof.Tactics.Exact (handleExact)
import MiniProver.Proof.Tactics.Intro (handleIntro)
import MiniProver.Proof.Tactics.Intros (handleIntros)
import MiniProver.Proof.Tactics.Destruct (handleDestruct)
import MiniProver.Proof.Tactics.Unfold (handleUnfold)
import MiniProver.Proof.Tactics.Apply (handleApply)

handleTactic :: Goal -> Tactic -> Either TacticError Result
handleTactic g@Goal{} e@Exact{} = handleExact g e
handleTactic g@Goal{} i@Intro{} = handleIntro g i
handleTactic g@Goal{} i@Intros{} = handleIntros g i
handleTactic g@Goal{} d@Destruct{} = handleDestruct g d
handleTactic g@Goal{} u@Unfold{} = handleUnfold g u
handleTactic g@Goal{} a@Apply{} = handleApply g a