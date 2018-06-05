module MiniProver.Proof.TacticDef where

import MiniProver.Core.Syntax

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