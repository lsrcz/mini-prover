{-# LANGUAGE LambdaCase #-}
module MiniProver.Proof.Tactics.ExactSpec where

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
  describe "exact" $ do
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
      allinoneAns = fromRight undefined $ handleTactic goal
        ( Exact
          ( TmLambda "T"
            TmType
          ( TmLambda "x1"
            ( TmRel "T" 0 )
            ( TmLambda "x2"
              ( TmRel "T" 1 )
              ( TmAppl
                [ TmLambda "T"
                    TmType
                  ( TmLambda "x"
                    ( TmRel "T" 0 )
                    ( TmConstr "eq_refl"
                      [ TmRel "T" 1
                      , TmRel "x" 0 ]))
                , TmRel "T" 2
                , TmRel "x2" 0 ])))))
    it "all in one -- goal" $
      getGoalList allinoneAns `shouldBe` []
    it "all in one -- func" $
      getResultFunc allinoneAns [] `shouldBe`
      TmLambda "T"
        TmType
      ( TmLambda "x1"
        ( TmRel "T" 0 )
        ( TmLambda "x2"
          ( TmRel "T" 1 )
          ( TmConstr "eq_refl"
            [ TmRel "T" 2
            , TmRel "x2" 0 ])))