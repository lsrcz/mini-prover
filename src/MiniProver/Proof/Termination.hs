module MiniProver.Proof.Termination where

import MiniProver.Core.Termination
import MiniProver.Core.Syntax
import MiniProver.Proof.ProofDef

computeDecParamTactic :: Tactic -> Either Term Tactic
computeDecParamTactic (Exact tm) = Exact <$> computeDecParam tm
computeDecParamTactic (Apply tm mbnm) = Apply <$> computeDecParam tm <*> Right mbnm
computeDecParamTactic (Destruct tm) = Destruct <$> computeDecParam tm
computeDecParamTactic (Induction tm) = Induction <$> computeDecParam tm
computeDecParamTactic (Rewrite b tm mbtm) = Rewrite b <$> computeDecParam tm <*>
  (case mbtm of
    Nothing -> Right Nothing
    Just tm1 -> case computeDecParam tm1 of
      Left err -> Left err
      Right tmdec -> Right (Just tmdec))
computeDecParamTactic tactic = Right tactic
