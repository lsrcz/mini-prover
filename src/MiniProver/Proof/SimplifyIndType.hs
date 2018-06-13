module MiniProver.Proof.SimplifyIndType (
    simplifyIndTactic
  ) where

import MiniProver.Core.Syntax
import MiniProver.Core.SimplifyIndType
import MiniProver.Proof.ProofDef

simplifyIndTactic :: Tactic -> Tactic
simplifyIndTactic (Exact tm) = Exact (simplifyIndType tm)
simplifyIndTactic (Apply tm mbnm) = Apply (simplifyIndType tm) mbnm
simplifyIndTactic (Destruct tm) = Destruct (simplifyIndType tm)
simplifyIndTactic (Induction tm) = Induction (simplifyIndType tm)
simplifyIndTactic (Rewrite b tm mbnm) = Rewrite b (simplifyIndType tm) mbnm
simplifyIndTactic (Exists tm) = Exists (simplifyIndType tm)
simplifyIndTactic tactic = tactic