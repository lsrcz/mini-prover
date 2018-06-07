{-# LANGUAGE LambdaCase #-}
module MiniProver.Proof.HandleTacticSpec where

import Test.Hspec
import Test.Hspec.Megaparsec
import MiniProver.Core.Syntax
import MiniProver.Core.Context
import MiniProver.Proof.HandleTactic
import MiniProver.Proof.ProofDef
import MiniProver.Utils.ContextForTesting

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
  describe "exact" $ do
    let
      goal = Goal 0 realEqContext $
        TmProd "T"
          TmType
        ( TmProd "_"
          ( TmRel "T" 0 )
          ( TmProd "m0"
            ( TmRel "T" 1 )
            ( TmIndType "eq"
              [ TmRel "T" 2
              , TmRel "m0" 0
              , TmRel "m0" 0 ])))
    it "all in one" $
      handleTactic goal
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
      `shouldSatisfy`
      (\case
          Left _ -> False
          Right (Result goallst f) ->
            null goallst &&
            f [] ==
              TmLambda "T"
                  TmType
                ( TmLambda "x1"
                  ( TmRel "T" 0 )
                  ( TmLambda "x2"
                    ( TmRel "T" 1 )
                    ( TmConstr "eq_refl"
                      [ TmRel "T" 2
                      , TmRel "x2" 0 ]))))
  describe "intro" $ do
    let
      goal = Goal 0 realEqContext $
        TmProd "T"
          TmType
        ( TmProd "_"
          ( TmRel "T" 0 )
          ( TmProd "m0"
            ( TmRel "T" 1 )
            ( TmIndType "eq"
              [ TmRel "T" 2
              , TmRel "m0" 0
              , TmRel "m0" 0 ])))
    it "no name" $
      handleTactic goal (Intro []) `shouldSatisfy`
      (\case
          Left _ -> False
          Right (Result goallst f) ->
            length goallst == 1 &&
            case head goallst of
              Goal i ctx1 ty -> i == 1 && ctx1 == (("T",VarBind TmType):realEqContext) &&
                ty == 
                  TmProd "_"
                    ( TmRel "T" 0 )
                    ( TmProd "m0"
                      ( TmRel "T" 1 )
                      ( TmIndType "eq"
                        [ TmRel "T" 2
                        , TmRel "m0" 0
                        , TmRel "m0" 0 ]))
            && f [TmVar "Goal1"] == TmLambda "T" TmType (TmVar "Goal1"))
    it "1 name" $
      handleTactic goal (Intro ["T1"]) `shouldSatisfy`
      (\case
          Left _ -> False
          Right (Result goallst f) ->
            length goallst == 1 &&
            case head goallst of
              Goal i ctx1 ty -> i == 1 && ctx1 == (("T1",VarBind TmType):realEqContext) &&
                ty == 
                  TmProd "_"
                    ( TmRel "T1" 0 )
                    ( TmProd "m0"
                      ( TmRel "T1" 1 )
                      ( TmIndType "eq"
                        [ TmRel "T1" 2
                        , TmRel "m0" 0
                        , TmRel "m0" 0 ]))
            && f [TmVar "Goal1"] == TmLambda "T1" TmType (TmVar "Goal1"))
    it "2 names" $
      handleTactic goal (Intro ["T1","m"]) `shouldSatisfy`
      (\case
          Left _ -> False
          Right (Result goallst f) ->
            length goallst == 1 &&
            case head goallst of
              Goal i ctx1 ty -> i == 1 && ctx1 == (("m",VarBind (TmRel "T1" 0)):("T1",VarBind TmType):realEqContext) &&
                ty == 
                  TmProd "m0"
                    ( TmRel "T1" 1 )
                    ( TmIndType "eq"
                      [ TmRel "T1" 2
                      , TmRel "m0" 0
                      , TmRel "m0" 0 ])
            && f [TmVar "Goal1"] == TmLambda "T1" TmType (TmLambda "m" (TmRel "T1" 0) (TmVar "Goal1")))
    it "4 names" $
      handleTactic goal (Intro ["a","b","c","d"]) `shouldSatisfy`
      (\case
        Left (TacticError str) -> str == "No enough products"
        Right _ -> False)
  describe "intros" $ do
    let
      goal = Goal 0 realEqContext $
        TmProd "T"
          TmType
        ( TmProd "_"
          ( TmRel "T" 0 )
          ( TmProd "m0"
            ( TmRel "T" 1 )
            ( TmIndType "eq"
              [ TmRel "T" 2
              , TmRel "m0" 0
              , TmRel "m0" 0 ])))
    it "all in one" $
      handleTactic goal Intros `shouldSatisfy`
        (\case
            Left _ -> False
            Right (Result goallst f) ->
              length goallst == 1 &&
              case head goallst of
                Goal i ctx1 ty -> i == 1 && ctx1 == (("m0",VarBind (TmRel "T1" 1)):("t",VarBind (TmRel "T1" 0)):("T1",VarBind TmType):realEqContext) &&
                  ty == 
                    TmIndType "eq"
                      [ TmRel "T1" 2
                      , TmRel "m0" 0
                      , TmRel "m0" 0 ]
              && f [TmVar "Goal1"] == TmLambda "T1" TmType (TmLambda "t" (TmRel "T1" 0) (TmLambda "m0" (TmRel "T1" 1) (TmVar "Goal1"))))