module MiniProver.Proof.ProofCommand where

import MiniProver.Core.Syntax

data ProofCommand =
    Proof
  | Undo
  | Restart
  | Admitted
  | Abort
  | Qed
  deriving (Show, Eq)
