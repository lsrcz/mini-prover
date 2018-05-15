module MiniProver.Core.ReductionSpec (main, spec) where

import Test.Hspec
import MiniProver.Core.Syntax
import MiniProver.Core.Reduction
import MiniProver.Utils.ContextForTesting

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
  describe "betaReduction" $ do
    it "2 terms" $
      betaReduction
      ( TmAppl
        [ TmLambda "x"
          ( TmIndType "nat" [] )
          ( TmAppl
            [ TmRel "plus" 1
            , TmRel "x" 0
            , TmConstr "S"
              [ TmRel "x" 0 ]])
        , TmConstr "S"
          [ TmRel "one" 1 ]])
      `shouldBe`
      TmAppl
      [ TmRel "plus" 0
      , TmConstr "S"
        [ TmRel "one" 1 ]
      , TmConstr "S"
        [ TmConstr "S"
          [ TmRel "one" 1 ]]]
    it "more terms" $
      betaReduction
      ( TmAppl
        [ TmLambda "x"
          ( TmIndType "nat" [] )
          ( TmLambda "y"
            ( TmIndType "nat" [] )
            ( TmAppl
              [ TmRel "plus" 2
              , TmRel "x" 1
              , TmRel "y" 0 ]))
        , TmRel "one" 4 
        , TmRel "two" 5 ])
      `shouldBe`
      TmAppl
      [ TmLambda "y"
        ( TmIndType "nat" [] )
        ( TmAppl
          [ TmRel "plus" 1
          , TmRel "one" 5
          , TmRel "y" 0 ])
      , TmRel "two" 5 ]
  describe "zetaReduction" $
    it "simple" $
      zetaReduction
      ( TmLetIn "x"
        ( TmIndType "nat" [] )
        ( TmRel "one" 1 )
        ( TmAppl
          [ TmRel "plus" 3
          , TmRel "one" 2
          , TmRel "x" 0 ]))
      `shouldBe`
      TmAppl
      [ TmRel "plus" 2
      , TmRel "one" 1
      , TmRel "one" 1 ]
  describe "iotaReduction" $ do
    it "iotaReduction-nat-O" $
      iotaReduction
      ( TmMatch
        ( TmConstr "O" [] )
        [ "nat" ]
        ( TmIndType "nat" [] )
        [ Equation
          [ "O" ]
          ( TmRel "a" 0)
        , Equation
          [ "S", "n" ]
          ( TmAppl
            [ TmRel "a" 1
            , TmRel "n" 0 ])])
      `shouldBe`
      TmRel "a" 0
    it "iotaReduction-nat-S" $
      iotaReduction
      ( TmMatch
        ( TmConstr "S" 
          [ TmRel "x" 2 ] )
        [ "nat" ]
        ( TmIndType "nat" [] )
        [ Equation
          [ "O" ]
          ( TmRel "a" 0)
        , Equation
          [ "S", "n" ]
          ( TmAppl
            [ TmRel "a" 1
            , TmRel "n" 0 ])])
      `shouldBe`
      TmAppl
        [ TmRel "a" 0
        , TmRel "x" 2 ]
    it "iotaReduction-list-nil" $
      iotaReduction
      ( TmMatch
        ( TmConstr "nil" [ TmIndType "nat" [] ] )
        [ "list", "T" ]
        ( TmIndType "list" [ TmIndType "list" [ TmRel "T" 0 ]])
        [ Equation
          [ "nil", "nat" ]
          ( TmConstr "nil"
            [ TmIndType "list"
              [ TmRel "nat" 0 ]])
        , Equation
          [ "cons", "nat", "x", "xs" ]
          ( TmConstr "cons"
            [ TmIndType "list"
              [ TmRel "nat" 2 ]
            , TmConstr "cons"
              [ TmRel "nat" 2
              , TmRel "x" 1
              , TmConstr "nil"
                [ TmRel "nat" 2 ]]
            , TmConstr "cons"
              [ TmIndType "list"
                [ TmRel "nat" 2 ]
              , TmRel "xs" 0
              , TmConstr "nil"
                [ TmIndType "list"
                  [ TmRel "nat" 2 ]]]])])
      `shouldBe`
      TmConstr "nil"
        [ TmIndType "list"
          [ TmIndType "nat" [] ]]
    it "iotaReduction-list-cons" $
      iotaReduction
      ( TmMatch
        ( TmConstr "cons" 
          [ TmIndType "nat" []
          , TmRel "one" 1
          , TmConstr "cons"
            [ TmIndType "nat" []
            , TmRel "two" 2
            , TmConstr "nil"
              [ TmIndType "nat" [] ]]])
        [ "list", "T" ]
        ( TmIndType "list" [ TmIndType "list" [ TmRel "T" 0 ]])
        [ Equation
          [ "nil", "nat" ]
          ( TmConstr "nil"
            [ TmIndType "list"
              [ TmRel "nat" 0 ]])
        , Equation
          [ "cons", "nat", "x", "xs" ]
          ( TmConstr "cons"
            [ TmIndType "list"
              [ TmRel "nat" 2 ]
            , TmConstr "cons"
              [ TmRel "nat" 2
              , TmRel "x" 1
              , TmConstr "nil"
                [ TmRel "nat" 2 ]]
            , TmConstr "cons"
              [ TmIndType "list"
                [ TmRel "nat" 2 ]
              , TmRel "xs" 0
              , TmConstr "nil"
                [ TmIndType "list"
                  [ TmRel "nat" 2 ]]]])])
      `shouldBe`
      TmConstr "cons"
        [ TmIndType "list"
          [ TmIndType "nat" [] ]
        , TmConstr "cons"
          [ TmIndType "nat" []
          , TmRel "one" 1
          , TmConstr "nil"
            [ TmIndType "nat" [] ]]
        , TmConstr "cons"
          [ TmIndType "list"
            [ TmIndType "nat" [] ]
          , TmConstr "cons"
            [ TmIndType "nat" []
            , TmRel "two" 2
            , TmConstr "nil"
              [ TmIndType "nat" [] ]]
          , TmConstr "nil"
            [ TmIndType "list"
              [ TmIndType "nat" [] ]]]]
  describe "deltaReduction" $
    it "dependentContext" $
      deltaReduction dependentContext (TmRel "C" 3)
      `shouldBe`
      TmRel "E" 5
  describe "etaExpansion" $
    it "simple" $
      etaExpansion (TmRel "t" 0) "x" (TmRel "T" 1)
      `shouldBe`
      TmLambda "x"
      ( TmRel "T" 1)
      ( TmAppl
        [ TmRel "t" 1
        , TmRel "x" 0 ])