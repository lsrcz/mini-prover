module MiniProver.Proof.Tactics.Destruct (
    handleDestruct
  ) where

import MiniProver.Proof.ProofDef
import MiniProver.Proof.Tactics.Intro
import MiniProver.Core.Typing
import MiniProver.Core.Context
import MiniProver.Core.Syntax
import MiniProver.PrettyPrint.PrettyPrint
import Data.Either (fromRight)
import Debug.Trace

handleDestruct :: Goal -> Tactic -> Either TacticError Result
handleDestruct (Goal d ctx ty) (Destruct tm) = undefined
