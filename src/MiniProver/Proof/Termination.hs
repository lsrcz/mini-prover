module MiniProver.Proof.Termination where

import MiniProver.Core.Termination
import MiniProver.Core.Syntax
import MiniProver.Proof.ProofDef

computeDecParamTactic :: Tactic -> Either Term Tactic
computeDecParamTactic (Exact tm) = Exact <$> computeDecParam tm