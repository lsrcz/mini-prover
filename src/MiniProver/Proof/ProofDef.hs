module MiniProver.Proof.ProofDef where

import MiniProver.Core.Syntax
import MiniProver.Core.Context

data ProofCommand =
    Proof
  | Undo
  | Restart
  | Admitted
  | Abort
  | Qed
  deriving (Show, Eq)

data Tactic =
    Exact Term
  | Apply Term (Maybe Name)
  | Intro [Name]
  | Intros
  | Destruct Term
  | Induction Term
  | Rewrite Bool Term (Maybe Term)
  | Simpl (Maybe Name)
  | Reflexivity
  | Symmetry
  deriving (Show, Eq)

data ProofInput =
    PCmd ProofCommand
  | PTac Tactic
  deriving (Show, Eq)

newtype TacticError = TacticError String

data Goal = Goal Int Context Term deriving (Show, Eq)

type ResultFunc = [Term] -> Term
data Result = Result [Goal] ResultFunc
