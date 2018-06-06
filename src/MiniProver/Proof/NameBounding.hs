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