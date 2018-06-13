module MiniProver.Proof.Termination where

import MiniProver.Core.Termination
import MiniProver.Core.Syntax
import MiniProver.Proof.ProofDef

computeDecParamTactic :: Tactic -> Either Term Tactic
computeDecParamTactic (Exact tm) = Exact <$> computeDecParam tm
computeDecParamTactic (Apply tm mbnm) = Apply <$> computeDecParam tm <*> Right mbnm
computeDecParamTactic (Destruct tm) = Destruct <$> computeDecParam tm
computeDecParamTactic (Induction tm) = Induction <$> computeDecParam tm
computeDecParamTactic (Rewrite b tm mbnm) = Rewrite b <$> computeDecParam tm <*>
  Right mbnm
computeDecParamTactic (Exists tm) = Exists <$> computeDecParam tm
computeDecParamTactic tactic = Right tactic
