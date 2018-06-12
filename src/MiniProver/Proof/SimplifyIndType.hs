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
simplifyIndTactic (Rewrite b tm mbtm) = Rewrite b (simplifyIndType tm) (simplifyIndType <$> mbtm)
simplifyIndTactic tactic = tactic