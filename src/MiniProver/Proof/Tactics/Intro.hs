module MiniProver.Proof.Tactics.Intro (
    handleIntro
  ) where

import MiniProver.Proof.ProofDef
import MiniProver.Core.Typing
import MiniProver.Core.Syntax
import MiniProver.PrettyPrint.PrettyPrint

handleIntro :: Goal -> Tactic -> Either TacticError Result
handleIntro (Goal _ ctx ty) (Intro lst) = undefined
