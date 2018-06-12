module MiniProver.Proof.Build where

import MiniProver.Core.Build
import MiniProver.Core.Context
import MiniProver.Proof.ProofDef

type BuiltTactic = Context -> Tactic

buildTactic :: Tactic -> BuiltTactic
buildTactic (Exact tm) ctx = Exact (buildTerm tm ctx)
buildTactic (Apply tm i) ctx = Apply (buildTerm tm ctx) i
buildTactic (Destruct tm) ctx = Destruct (buildTerm tm ctx)
buildTactic (Induction tm) ctx = Induction (buildTerm tm ctx)
buildTactic (Rewrite b tm mbnm) ctx =
  Rewrite b (buildTerm tm ctx) mbnm
buildTactic tactic _ = tactic
