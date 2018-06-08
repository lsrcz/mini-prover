{-# LANGUAGE LambdaCase #-}
module MiniProver.Proof.Tactics.IntroSpec where

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
  describe "intro" $ do
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
      nonameAns = fromRight undefined $ handleTactic goal (Intro [])
    it "no name -- goal" $
      getGoalList nonameAns `shouldBe`
      [ Goal 1 (("T",VarBind TmType):realEqContext)
        ( TmProd "_"
          ( TmRel "T" 0 )
          ( TmProd "m"
            ( TmRel "T" 1 )
            ( TmIndType "eq"
              [ TmRel "T" 2
              , TmRel "m" 0
              , TmRel "m" 0 ])))]
    it "no name -- func" $
      getResultFunc nonameAns [TmVar "Goal1"] `shouldBe`
        TmLambda "T" TmType (TmVar "Goal1")
    let onenameAns = fromRight undefined $ handleTactic goal (Intro ["T1"])
    it "one name -- goal" $
      getGoalList onenameAns `shouldBe`
      [ Goal 1 (("T1",VarBind TmType):realEqContext)
        ( TmProd "_"
          ( TmRel "T1" 0 )
          ( TmProd "m"
            ( TmRel "T1" 1 )
            ( TmIndType "eq"
              [ TmRel "T1" 2
              , TmRel "m" 0
              , TmRel "m" 0 ])))]
    it "one name -- func" $
      getResultFunc onenameAns [TmVar "Goal1"] `shouldBe`
        TmLambda "T1" TmType (TmVar "Goal1")
    let twonamesAns = fromRight undefined $ handleTactic goal (Intro ["T1","m"])
    it "two names -- goal" $
      getGoalList twonamesAns `shouldBe`
      [ Goal 2 (("m",VarBind (TmRel "T1" 0)):("T1",VarBind TmType):realEqContext)
        ( TmProd "m0"
          ( TmRel "T1" 1 )
          ( TmIndType "eq"
            [ TmRel "T1" 2
            , TmRel "m0" 0
            , TmRel "m0" 0 ]))]
    it "two names -- func" $
      getResultFunc twonamesAns [TmVar "Goal1"] `shouldBe`
        TmLambda "T1" TmType (TmLambda "m" (TmRel "T1" 0) (TmVar "Goal1"))
    it "four names -- should fail" $
      handleTactic goal (Intro ["a","b","c","d"]) `shouldSatisfy`
      (\case
        Left (TacticError str) -> str == "No enough products"
        Right _ -> False)