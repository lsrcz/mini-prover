module MiniProver.Proof.NameBounding (
    NameBoundStatus(..)
  , checkAllNameBoundedTactic
  ) where

import MiniProver.Core.Syntax
import MiniProver.Proof.ProofDef
import MiniProver.Core.Context
import MiniProver.Core.NameBounding

checkAllNameBoundedTactic :: Context -> Tactic -> NameBoundStatus
checkAllNameBoundedTactic ctx (Exact tm) = checkAllNameBounded ctx tm
checkAllNameBoundedTactic ctx (Apply tm _) = checkAllNameBounded ctx tm
checkAllNameBoundedTactic ctx (Destruct tm) = checkAllNameBounded ctx tm
checkAllNameBoundedTactic ctx (Induction tm) = checkAllNameBounded ctx tm
checkAllNameBoundedTactic ctx (Rewrite _ tm _) =
  checkAllNameBounded ctx tm
checkAllNameBoundedTactic ctx (Exists tm) = checkAllNameBounded ctx tm
checkAllNameBoundedTactic _ _ = AllNameBounded