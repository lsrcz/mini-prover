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
    it "Prod-2terms" $
      betaReduction
      ( TmAppl
        [ TmProd "x"
          ( TmIndType "nat" [] )
          ( TmIndType "eq"
            [ TmIndType "nat" []
            , TmRel "x" 0
            , TmRel "x" 0 ])
        , TmRel "one" 0])
      `shouldBe`
      TmIndType "eq"
      [ TmIndType "nat" []
      , TmRel "one" 0
      , TmRel "one" 0 ]
    it "Prod-more terms" $
      betaReduction
      ( TmAppl
        [ TmProd "x"
          ( TmIndType "nat" [] )
          ( TmProd "y"
            ( TmIndType "nat" [] )
            ( TmProd "H"
              ( TmIndType "eq"
                [ TmIndType "nat" []
                , TmRel "x" 1
                , TmRel "y" 0 ])
              ( TmIndType "eq"
                [ TmIndType "nat" []
                , TmRel "y" 1
                , TmRel "x" 2 ])))
        , TmRel "one" 1
        , TmRel "two" 2 ])
      `shouldBe`
      TmAppl
      [ TmProd "y"
        ( TmIndType "nat" [] )
        ( TmProd "H"
          ( TmIndType "eq"
            [ TmIndType "nat" []
            , TmRel "one" 2
            , TmRel "y" 0 ])
          ( TmIndType "eq"
            [ TmIndType "nat" []
            , TmRel "y" 1
            , TmRel "one" 3 ]))
      , TmRel "two" 2 ]
    it "fixpoint" $
      betaReduction
      ( TmAppl
        [ TmFix 1
          ( TmLambda "plus"
            ( TmProd "a"
              ( TmIndType "nat" [])
              ( TmProd "b"
                ( TmIndType "nat" [])
                ( TmIndType "nat" [])))
            ( TmLambda "a"
              ( TmIndType "nat" [])
              ( TmLambda "b"
                ( TmIndType "nat" [])
                ( TmMatch 0
                  ( TmRel "a" 1)
                    "x0"
                    [ "nat" ]
                    ( TmIndType "nat" [])
                    [ Equation ["O"] (TmRel "b" 0)
                    , Equation ["S","n"]
                      ( TmAppl
                        [ TmLambda ".0"
                          ( TmIndType "nat" [])
                          ( TmConstr "S" [TmRel ".0" 0])
                        , TmAppl
                          [ TmRel "plus" 3
                          , TmRel "n" 0
                          , TmRel "b" 1]])]))))
        , TmConstr "O" [] ])
      `shouldBe`
      TmLambda "b"
      ( TmIndType "nat" [] )
      ( TmMatch 0
        ( TmConstr "O" [] )
        "x0"
        [ "nat" ]
        ( TmIndType "nat" [])
        [ Equation ["O"] (TmRel "b" 0)
        , Equation ["S","n"]
          ( TmAppl
            [ TmLambda ".0"
              ( TmIndType "nat" [])
              ( TmConstr "S" [TmRel ".0" 0])
            , TmAppl
              [ TmFix 1
                ( TmLambda "plus"
                  ( TmProd "a"
                    ( TmIndType "nat" [])
                    ( TmProd "b"
                      ( TmIndType "nat" [])
                      ( TmIndType "nat" [])))
                  ( TmLambda "a"
                    ( TmIndType "nat" [])
                    ( TmLambda "b"
                      ( TmIndType "nat" [])
                      ( TmMatch 0
                        ( TmRel "a" 1)
                        "x0"
                        [ "nat" ]
                        ( TmIndType "nat" [])
                        [ Equation ["O"] (TmRel "b" 0)
                        , Equation ["S","n"]
                          ( TmAppl
                            [ TmLambda ".0"
                              ( TmIndType "nat" [])
                              ( TmConstr "S" [TmRel ".0" 0])
                            , TmAppl
                              [ TmRel "plus" 3
                              , TmRel "n" 0
                              , TmRel "b" 1]])]))))
              , TmRel "n" 0
              , TmRel "b" 1 ]])])
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
      ( TmMatch 0
        ( TmConstr "O" [] )
        "x0"
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
      ( TmMatch 0
        ( TmConstr "S" 
          [ TmRel "x" 2 ] )
        "x0"
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
      ( TmMatch 1
        ( TmConstr "nil" [ TmIndType "nat" [] ] )
        "l0"
        [ "list", "_" ]
        ( TmIndType "list" [ TmIndType "list" [ TmIndType "nat" [] ]])
        [ Equation
          [ "nil", "_" ]
          ( TmConstr "nil"
            [ TmIndType "list"
              [ TmIndType "nat" [] ]])
        , Equation
          [ "cons", "_", "x", "xs" ]
          ( TmConstr "cons"
            [ TmIndType "list"
              [ TmIndType "nat" [] ]
            , TmConstr "cons"
              [ TmIndType "nat" []
              , TmRel "x" 1
              , TmConstr "nil"
                [ TmIndType "nat" [] ]]
            , TmConstr "cons"
              [ TmIndType "list"
                [ TmIndType "nat" [] ]
              , TmRel "xs" 0
              , TmConstr "nil"
                [ TmIndType "list"
                  [ TmIndType "nat" [] ]]]])])
      `shouldBe`
      TmConstr "nil"
        [ TmIndType "list"
          [ TmIndType "nat" [] ]]
    it "iotaReduction-list-cons" $
      iotaReduction
      ( TmMatch 1
        ( TmConstr "cons" 
          [ TmIndType "nat" []
          , TmRel "one" 1
          , TmConstr "cons"
            [ TmIndType "nat" []
            , TmRel "two" 2
            , TmConstr "nil"
              [ TmIndType "nat" [] ]]])
        "l0"
        [ "list", "_" ]
        ( TmIndType "list" [ TmIndType "list" [ TmIndType "nat" [] ]])
        [ Equation
          [ "nil", "_" ]
          ( TmConstr "nil"
            [ TmIndType "list"
              [ TmIndType "nat" [] ]])
        , Equation
          [ "cons", "_", "x", "xs" ]
          ( TmConstr "cons"
            [ TmIndType "list"
              [ TmIndType "nat" [] ]
            , TmConstr "cons"
              [ TmIndType "nat" []
              , TmRel "x" 1
              , TmConstr "nil"
                [ TmIndType "nat" [] ]]
            , TmConstr "cons"
              [ TmIndType "list"
                [ TmIndType "nat" [] ]
              , TmRel "xs" 0
              , TmConstr "nil"
                [ TmIndType "list"
                  [ TmIndType "nat" [] ]]]])])
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
  describe "strategyToIntBits" $ do
    it "simple-1" $
      strategyToIntBits BetaAppl `shouldBe` 1
    it "simple-2" $
      strategyToIntBits BetaFix `shouldBe` 256
    it "simple-3" $
      strategyToIntBits BetaInMatchBranch `shouldBe` 65536
    it "simple-4" $
      strategyToIntBits ZetaInMatchBranch `shouldBe` 1024
  describe "intBitsToStrategy" $ do
    it "simple-1" $
      intBitsToStrategy 1 `shouldBe` BetaAppl
    it "simple-2" $
      intBitsToStrategy 128 `shouldBe` BetaInLambdaTm
    it "simple-3" $
      intBitsToStrategy 32768 `shouldBe` BetaInMatchTm
    it "simple-4" $
      intBitsToStrategy 1024 `shouldBe` ZetaInMatchBranch
  describe "strategyListToSet" $
    it "beta" $
      strategyListToSet
      [ BetaAppl
      , BetaInProdTy
      , BetaFix
      , BetaInMatchBranch]
      `shouldBe`
      65801
  describe "hasStrategy" $ do
    let 
      betaStrategy = strategyListToSet
        [ BetaAppl
        , BetaInProdTy
        , BetaFix
        , BetaInMatchBranch]
    it "in the set" $
      hasStrategy betaStrategy BetaAppl `shouldBe` True
    it "in the set 2" $
      hasStrategy betaStrategy BetaInMatchBranch `shouldBe` True
    it "not in the set" $
      hasStrategy betaStrategy BetaProd `shouldBe` False
    it "not in the set 2" $
      hasStrategy betaStrategy BetaLambda `shouldBe` False
  describe "hasStrategyInSet" $ do
    let
      strategySet =
        StrategySet
        ( strategyListToSet
          [ BetaAppl
          , BetaProd
          , BetaFix
          , BetaInMatchBranch ])
        ( strategyListToSet
          [ ZetaLetIn
          , ZetaInConstr ])
        ( strategyListToSet
          [ IotaMatch
          , IotaInConstr
          , IotaInConstr ])
        ( strategyListToSet
          [ DeltaRel ])
    it "beta in set" $
      hasStrategyInSet strategySet BetaFix `shouldBe` True
    it "beta not in set" $
      hasStrategyInSet strategySet BetaInFix `shouldBe` False
    it "zeta in set" $
      hasStrategyInSet strategySet ZetaLetIn `shouldBe` True
    it "zeta not in set" $
      hasStrategyInSet strategySet ZetaInFix `shouldBe` False
    it "iota in set" $
      hasStrategyInSet strategySet IotaInConstr `shouldBe` True
    it "iota not in set" $
      hasStrategyInSet strategySet IotaInAppl `shouldBe` False
    it "delta in set" $
      hasStrategyInSet strategySet DeltaRel `shouldBe` True
    it "delta not in set" $
      hasStrategyInSet strategySet DeltaInAppl `shouldBe` False
  describe "clear sets" $ do
    let
      strategySet =
        StrategySet
        ( strategyListToSet
          [ BetaAppl
          , BetaProd
          , BetaFix
          , BetaInMatchBranch ])
        ( strategyListToSet
          [ ZetaLetIn
          , ZetaInConstr ])
        ( strategyListToSet
          [ IotaMatch
          , IotaInConstr
          , IotaInConstr ])
        ( strategyListToSet
          [ DeltaRel ])
    it "clearBetaSet" $
      clearBetaSet strategySet `shouldBe` 
        StrategySet
        0
        ( strategyListToSet
          [ ZetaLetIn
          , ZetaInConstr ])
        ( strategyListToSet
          [ IotaMatch
          , IotaInConstr
          , IotaInConstr ])
        ( strategyListToSet
          [ DeltaRel ])
    it "clearZetaSet" $
      clearZetaSet strategySet `shouldBe` 
        StrategySet
        ( strategyListToSet
          [ BetaAppl
          , BetaProd
          , BetaFix
          , BetaInMatchBranch ])
        0
        ( strategyListToSet
          [ IotaMatch
          , IotaInConstr
          , IotaInConstr ])
        ( strategyListToSet
          [ DeltaRel ])
    it "clearIotaSet" $
      clearIotaSet strategySet `shouldBe` 
        StrategySet
        ( strategyListToSet
          [ BetaAppl
          , BetaProd
          , BetaFix
          , BetaInMatchBranch ])
        ( strategyListToSet
          [ ZetaLetIn
          , ZetaInConstr ])
        0
        ( strategyListToSet
          [ DeltaRel ])
    it "clearDeltaSet" $
      clearDeltaSet strategySet `shouldBe` 
        StrategySet
        ( strategyListToSet
          [ BetaAppl
          , BetaProd
          , BetaFix
          , BetaInMatchBranch ])
        ( strategyListToSet
          [ ZetaLetIn
          , ZetaInConstr ])
        ( strategyListToSet
          [ IotaMatch
          , IotaInConstr
          , IotaInConstr ])
        0
    it "clearBetaIfUnset-unset" $
      clearBetaIfUnset BetaInLetInTy strategySet `shouldBe` 
        StrategySet
        0
        ( strategyListToSet
          [ ZetaLetIn
          , ZetaInConstr ])
        ( strategyListToSet
          [ IotaMatch
          , IotaInConstr
          , IotaInConstr ])
        ( strategyListToSet
          [ DeltaRel ])
    it "clearZetaIfUnset-unset" $
      clearZetaIfUnset ZetaInFix strategySet `shouldBe` 
        StrategySet
        ( strategyListToSet
          [ BetaAppl
          , BetaProd
          , BetaFix
          , BetaInMatchBranch ])
        0
        ( strategyListToSet
          [ IotaMatch
          , IotaInConstr
          , IotaInConstr ])
        ( strategyListToSet
          [ DeltaRel ])
    it "clearIotaIfUnset-unset" $
      clearIotaIfUnset IotaInFix strategySet `shouldBe` 
        StrategySet
        ( strategyListToSet
          [ BetaAppl
          , BetaProd
          , BetaFix
          , BetaInMatchBranch ])
        ( strategyListToSet
          [ ZetaLetIn
          , ZetaInConstr ])
        0
        ( strategyListToSet
          [ DeltaRel ])
    it "clearDeltaIfUnset-unset" $
      clearDeltaIfUnset DeltaInFix strategySet `shouldBe` 
        StrategySet
        ( strategyListToSet
          [ BetaAppl
          , BetaProd
          , BetaFix
          , BetaInMatchBranch ])
        ( strategyListToSet
            [ ZetaLetIn
            , ZetaInConstr ])
        ( strategyListToSet
          [ IotaMatch
          , IotaInConstr
          , IotaInConstr ])
        0
    it "clearBetaIfUnset-set" $
      clearBetaIfUnset BetaInMatchBranch strategySet `shouldBe`
        StrategySet
        ( strategyListToSet
          [ BetaAppl
          , BetaProd
          , BetaFix
          , BetaInMatchBranch ])
        ( strategyListToSet
          [ ZetaLetIn
          , ZetaInConstr ])
        ( strategyListToSet
          [ IotaMatch
          , IotaInConstr
          , IotaInConstr ])
        ( strategyListToSet
          [ DeltaRel ])
    it "clearZetaIfUnset-set" $
      clearZetaIfUnset ZetaInConstr strategySet `shouldBe`
        StrategySet
        ( strategyListToSet
          [ BetaAppl
          , BetaProd
          , BetaFix
          , BetaInMatchBranch ])
        ( strategyListToSet
          [ ZetaLetIn
          , ZetaInConstr ])
        ( strategyListToSet
          [ IotaMatch
          , IotaInConstr
          , IotaInConstr ])
        ( strategyListToSet
          [ DeltaRel ])
    it "clearIotaIfUnset-set" $
      clearIotaIfUnset IotaInConstr strategySet `shouldBe`
        StrategySet
        ( strategyListToSet
          [ BetaAppl
          , BetaProd
          , BetaFix
          , BetaInMatchBranch ])
        ( strategyListToSet
          [ ZetaLetIn
          , ZetaInConstr ])
        ( strategyListToSet
          [ IotaMatch
          , IotaInConstr
          , IotaInConstr ])
        ( strategyListToSet
          [ DeltaRel ])
    it "clearDeltaIfUnset-set" $
      clearDeltaIfUnset DeltaRel strategySet `shouldBe`
        StrategySet
        ( strategyListToSet
          [ BetaAppl
          , BetaProd
          , BetaFix
          , BetaInMatchBranch ])
        ( strategyListToSet
          [ ZetaLetIn
          , ZetaInConstr ])
        ( strategyListToSet
          [ IotaMatch
          , IotaInConstr
          , IotaInConstr ])
        ( strategyListToSet
          [ DeltaRel ])
  describe "strategy contents" $ do
    it "fullBetaStrategy" $
      fullBetaStrategy `shouldBe` 131071
    it "fullZetaStrategy" $
      fullZetaStrategy `shouldBe` 2047
    it "fullIotaStrategy" $
      fullIotaStrategy `shouldBe` 16383
    it "fullDeltaStrategy" $
      fullDeltaStrategy `shouldBe` 16383
  describe "reductionWithStrategy" $
    describe "full reduction" $ do
      let
        strategySet = StrategySet
          fullBetaStrategy
          fullZetaStrategy
          fullIotaStrategy
          fullDeltaStrategy
      let 
        fullReductionForTest =
          reductionWithStrategy strategySet natContextWithPredefinedFunctions
      describe "simple terms" $ do
        it "plus" $
          fullReductionForTest (TmRel "plus" 9)
          `shouldBe`
          TmFix 1
          ( TmLambda "plus"
            ( TmProd "a"
              ( TmIndType "nat" [] )
              ( TmProd "b"
                ( TmIndType "nat" [] )
                ( TmIndType "nat" [] )))
            ( TmLambda "a"
              ( TmIndType "nat" [] )
              ( TmLambda "b"
                ( TmIndType "nat" [] )
                ( TmMatch 0
                  ( TmRel "a" 1 )
                  "a0"
                  [ "nat" ]
                  ( TmIndType "nat" [] )
                  [ Equation
                    [ "O" ]
                    ( TmRel "b" 0 )
                  , Equation
                    [ "S", "n" ]
                    ( TmAppl
                      [ TmRel "plus" 3
                      , TmRel "n" 0
                      , TmConstr "S" [ TmRel "b" 1 ]])]))))
        it "two" $
          fullReductionForTest ( TmRel "two" 6 )
          `shouldBe`
          TmConstr "S"
          [ TmConstr "S"
            [ TmConstr "O" [] ]]
        it "pred" $
          fullReductionForTest ( TmRel "pred" 5 )
          `shouldBe`
          TmLambda "x"
          ( TmIndType "nat" [] )
          ( TmMatch 0
            ( TmRel "x" 0 )
            "x0"
            [ "nat" ]
            ( TmIndType "nat" [] )
            [ Equation
              [ "O" ]
              ( TmConstr "O" [] )
            , Equation
              [ "S", "n" ]
              ( TmRel "n" 0 )])
        it "succ" $
          fullReductionForTest ( TmRel "succ" 4 )
          `shouldBe`
          TmLambda "x"
          ( TmIndType "nat" [] )
          ( TmConstr "S" [ TmRel "x" 0 ])
        it "succtwo" $
          fullReductionForTest ( TmRel "succtwo" 3 )
          `shouldBe`
          TmLambda "x"
          ( TmIndType "nat" [] )
          ( TmConstr "S" [ TmConstr "S" [ TmRel "x" 0 ]])
        it "succthreeLetIn" $
          fullReductionForTest ( TmRel "succthreeLetIn" 2 )
          `shouldBe`
          TmLambda "x"
          ( TmIndType "nat" [] )
          ( TmConstr "S" [ TmConstr "S" [ TmConstr "S" [ TmRel "x" 0 ]]])
        it "succByPlus" $
          fullReductionForTest ( TmRel "succByPlus" 1 )
          `shouldBe`
          TmLambda "b"
          ( TmIndType "nat" [] )
          ( TmConstr "S" [ TmRel "b" 0 ])
        it "plusThreeNumbers" $
          fullReductionForTest ( TmRel "plusThreeNumbers" 0 )
          `shouldBe`
          TmLambda "x"
          ( TmIndType "nat" [])
          ( TmLambda "y"
            ( TmIndType "nat" [])
            ( TmLambda "z"
              ( TmIndType "nat" [])
              ( TmMatch 0
                ( TmRel "x" 2 )
                "a0"
                [ "nat" ]
                ( TmIndType "nat" [])
                [ Equation
                  [ "O" ]
                  ( TmMatch 0
                    ( TmRel "y" 1 )
                    "a0"
                    [ "nat" ]
                    ( TmIndType "nat" [])
                    [ Equation
                      [ "O" ]
                      ( TmRel "z" 0 )
                    , Equation
                      [ "S"
                      , "n" ]
                      ( TmAppl
                        [ TmFix 1
                          ( TmLambda "plus"
                            ( TmProd "a"
                              ( TmIndType "nat" [])
                              ( TmProd "b"
                                ( TmIndType "nat" [])
                                ( TmIndType "nat" [])))
                            ( TmLambda "a"
                              ( TmIndType "nat" [])
                              ( TmLambda "b"
                                ( TmIndType "nat" [])
                                ( TmMatch 0
                                  ( TmRel "a" 1 )
                                  "a0"
                                  [ "nat" ]
                                  ( TmIndType "nat" [])
                                  [ Equation
                                    [ "O" ]
                                    ( TmRel "b" 0 )
                                  , Equation
                                    [ "S"
                                    , "n" ]
                                    ( TmAppl
                                      [ TmRel "plus" 3
                                      , TmRel "n" 0
                                      , TmConstr "S"
                                        [ TmRel "b" 1 ]])]))))
                        , TmRel "n" 0
                        , TmConstr "S"
                          [ TmRel "z" 1 ]])])
                , Equation
                  [ "S"
                  , "n" ]
                  ( TmAppl
                    [ TmFix 1
                      ( TmLambda "plus"
                        ( TmProd "a"
                          ( TmIndType "nat" [])
                          ( TmProd "b"
                            ( TmIndType "nat" [])
                            ( TmIndType "nat" [])))
                        ( TmLambda "a"
                          ( TmIndType "nat" [])
                          ( TmLambda "b"
                            ( TmIndType "nat" [])
                            ( TmMatch 0
                              ( TmRel "a" 1 )
                              "a0"
                              [ "nat" ]
                              ( TmIndType "nat" [])
                              [ Equation
                                [ "O" ]
                                ( TmRel "b" 0 )
                              , Equation
                                [ "S"
                                , "n" ]
                                ( TmAppl
                                  [ TmRel "plus" 3
                                  , TmRel "n" 0
                                  , TmConstr "S"
                                    [ TmRel "b" 1 ]])]))))
                    , TmRel "n" 0
                    , TmConstr "S"
                      [ TmMatch 0
                        ( TmRel "y" 2 )
                        "a0"
                        [ "nat" ]
                        ( TmIndType "nat" [])
                        [ Equation
                          [ "O" ]
                          ( TmRel "z" 1 )
                        , Equation
                          [ "S"
                          , "n" ]
                          ( TmAppl
                            [ TmFix 1
                              ( TmLambda "plus"
                                ( TmProd "a"
                                  ( TmIndType "nat" [])
                                  ( TmProd "b"
                                    ( TmIndType "nat" [])
                                    ( TmIndType "nat" [])))
                                ( TmLambda "a"
                                  ( TmIndType "nat" [])
                                  ( TmLambda "b"
                                    ( TmIndType "nat" [])
                                    ( TmMatch 0
                                      ( TmRel "a" 1 )
                                      "a0"
                                      [ "nat" ]
                                      ( TmIndType "nat" [])
                                      [ Equation
                                        [ "O" ]
                                        ( TmRel "b" 0 )
                                      , Equation
                                        [ "S"
                                        , "n" ]
                                        ( TmAppl
                                          [ TmRel "plus" 3
                                          , TmRel "n" 0
                                          , TmConstr "S"
                                            [ TmRel "b" 1 ]])]))))
                            , TmRel "n" 0
                            , TmConstr "S"
                              [ TmRel "z" 2 ]])]]])])))
        it "pred two" $
          fullReductionForTest ( TmAppl [ TmRel "pred" 5, TmRel "two" 6 ])
          `shouldBe`
          TmConstr "S" [ TmConstr "O" [] ]
        it "succ two" $
          fullReductionForTest ( TmAppl [ TmRel "succ" 4, TmRel "two" 6 ])
          `shouldBe`
          TmConstr "S"
          [ TmConstr "S"
            [ TmConstr "S"
              [ TmConstr "O" [] ]]]
        it "succthreeLetIn zero" $
          fullReductionForTest ( TmAppl [ TmRel "succthreeLetIn" 2, TmRel "zero" 8 ])
          `shouldBe`
          TmConstr "S"
          [ TmConstr "S"
            [ TmConstr "S"
              [ TmConstr "O" [] ]]]
        it "succByPlus two" $
          fullReductionForTest ( TmAppl [ TmRel "succByPlus" 1, TmRel "two" 6 ])
          `shouldBe`
          TmConstr "S"
          [ TmConstr "S"
            [ TmConstr "S"
              [ TmConstr "O" [] ]]]
        it "plusThreeNumbers-partial-1-zero" $
          fullReductionForTest ( TmAppl [ TmRel "plusThreeNumbers" 0, TmRel "zero" 8 ])
          `shouldBe`
          TmLambda "y"
            ( TmIndType "nat" [])
            ( TmLambda "z"
              ( TmIndType "nat" [])
              ( TmMatch 0
                ( TmRel "y" 1 )
                "a0"
                [ "nat" ]
                ( TmIndType "nat" [])
                [ Equation
                  [ "O" ]
                  ( TmRel "z" 0 )
                , Equation
                  [ "S"
                  , "n" ]
                  ( TmAppl
                    [ TmFix 1
                      ( TmLambda "plus"
                        ( TmProd "a"
                          ( TmIndType "nat" [])
                          ( TmProd "b"
                            ( TmIndType "nat" [])
                            ( TmIndType "nat" [])))
                        ( TmLambda "a"
                          ( TmIndType "nat" [])
                          ( TmLambda "b"
                            ( TmIndType "nat" [])
                            ( TmMatch 0
                              ( TmRel "a" 1 )
                              "a0"
                              [ "nat" ]
                              ( TmIndType "nat" [])
                              [ Equation
                                [ "O" ]
                                ( TmRel "b" 0 )
                              , Equation
                                [ "S"
                                , "n" ]
                                ( TmAppl
                                  [ TmRel "plus" 3
                                  , TmRel "n" 0
                                  , TmConstr "S"
                                    [ TmRel "b" 1 ]])]))))
                    , TmRel "n" 0
                    , TmConstr "S"
                      [ TmRel "z" 1 ]])]))
        it "plusThreeNumbers-partial-1-one" $
          fullReductionForTest ( TmAppl [ TmRel "plusThreeNumbers" 0, TmRel "one" 7 ])
          `shouldBe`
          TmLambda "y"
          ( TmIndType "nat" [] )
          ( TmLambda "z"
            ( TmIndType "nat" [] )
            ( TmConstr "S"
              [ TmMatch 0
                ( TmRel "y" 1 )
                "a0"
                [ "nat" ]
                ( TmIndType "nat" [] )
                [ Equation
                  [ "O" ]
                  ( TmRel "z" 0 )
                , Equation
                  [ "S", "n" ]
                  ( TmAppl
                    [ TmFix 1
                      ( TmLambda "plus"
                        ( TmProd "a"
                          ( TmIndType "nat" [] )
                          ( TmProd "b"
                            ( TmIndType "nat" [] )
                            ( TmIndType "nat" [] )))
                        ( TmLambda "a"
                          ( TmIndType "nat" [] )
                          ( TmLambda "b"
                            ( TmIndType "nat" [] )
                            ( TmMatch 0
                              ( TmRel "a" 1 )
                              "a0"
                              [ "nat" ]
                              ( TmIndType "nat" [] )
                              [ Equation
                                [ "O" ]
                                ( TmRel "b" 0 )
                              , Equation
                                [ "S", "n" ]
                                ( TmAppl
                                  [ TmRel "plus" 3
                                  , TmRel "n" 0
                                  , TmConstr "S"
                                    [ TmRel "b" 1 ]])]))))
                    , TmRel "n" 0
                    , TmConstr "S"
                      [ TmRel "z" 1 ]])]]))
        it "plusThreeNumbers-partial-2-two-two" $
          fullReductionForTest ( TmAppl [ TmRel "plusThreeNumbers" 0, TmRel "two" 6, TmRel "two" 6 ])
          `shouldBe`
          TmLambda "z"
          ( TmIndType "nat" [] )
          ( TmConstr "S"
            [ TmConstr "S"
              [ TmConstr "S"
                [ TmConstr "S"
                  [ TmRel "z" 0 ]]]])
        it "plusThreeNumbers-full-two-two-two" $
          fullReductionForTest 
            ( TmAppl 
              [ TmRel "plusThreeNumbers" 0
              , TmRel "two" 6
              , TmRel "two" 6
              , TmRel "two" 6 ])
          `shouldBe`
          TmConstr "S"
          [ TmConstr "S"
            [ TmConstr "S"
              [ TmConstr "S"
                [ TmConstr "S"
                  [ TmConstr "S"
                    [ TmConstr "O" [] ]]]]]]
          