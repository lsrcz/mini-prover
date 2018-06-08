{-# LANGUAGE LambdaCase #-}
module MiniProver.Proof.Tactics.IntrosSpec where

import Test.Hspec
import Test.Hspec.Megaparsec
import MiniProver.Core.Syntax
import MiniProver.Core.Context
import MiniProver.Proof.HandleTactic
import MiniProver.Proof.ProofDef
import MiniProver.Utils.ContextForTesting
import Data.Either (fromRight)
import Debug.Trace

main :: IO ()
main = hspec spec

spec :: Spec
spec =
  describe "intros" $ do
    let
      goal = Goal 0 realEqContext $
        TmProd "T"
          TmType
        ( TmProd "_"
          ( TmRel "T" 0 )
          ( TmProd "m"
            ( TmRel "T" 1 )
            ( TmIndType "eq"
              [ TmRel "T" 2
              , TmRel "m" 0
              , TmRel "m" 0 ])))
      allinoneAns = fromRight undefined $ handleTactic goal Intros
    it "all in one -- goal" $
      getGoalList allinoneAns `shouldBe`
      [ Goal 3 (("m",VarBind (TmRel "T" 1)):("t",VarBind (TmRel "T" 0)):("T",VarBind TmType):realEqContext)
        ( TmIndType "eq"
          [ TmRel "T" 2
          , TmRel "m" 0
          , TmRel "m" 0 ])]
    it "all in one -- func" $
      getResultFunc allinoneAns [TmVar "Goal1"] `shouldBe`
        TmLambda "T" TmType (TmLambda "t" (TmRel "T" 0) (TmLambda "m" (TmRel "T" 1) (TmVar "Goal1")))