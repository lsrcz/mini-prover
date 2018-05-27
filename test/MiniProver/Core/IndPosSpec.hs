module MiniProver.Core.IndPosSpec (main, spec) where

import           MiniProver.Core.Context
import           MiniProver.Core.IndPos
import           MiniProver.Core.Syntax
import           MiniProver.Utils.ContextForTesting
import           Test.Hspec

main :: IO ()
main = hspec spec

spec :: Spec
spec =
  describe "positivity" $ do
    it "le-yes" $
      isPositive natContext
      (Ind "le" 1
            (TmProd "x"
              (TmIndType "nat" [])
              (TmProd "_"
                (TmIndType "nat" [])
                TmType))
            (TmLambda "x"
              (TmIndType "nat" [])
              (TmLambda ".0"
                (TmIndType "nat" [])
                (TmIndType "le" [TmRel "x" 1, TmRel ".0" 0])))
            [ ( "lerefl"
              , TmProd "x"
                  (TmIndType "nat" [])
                  (TmIndType "le" [TmRel "x" 0, TmRel "x" 0])
              , TmLambda "x"
                  (TmIndType "nat" [])
                  (TmConstr "lerefl" [TmRel "x" 0]))
            , ( "leS"
              , TmProd "x"
                  (TmIndType "nat" [])
                  (TmProd "y"
                    (TmIndType "nat" [])
                    (TmProd "_"
                      (TmIndType "le" [TmRel "x" 1, TmRel "y" 0])
                      (TmIndType "le"
                        [ TmRel "x" 2
                        , TmAppl
                          [ TmLambda ".0"
                            ( TmIndType "nat" [] )
                            ( TmConstr "S" [ TmRel ".0" 0 ])
                        , TmRel "y" 1]])))
              , TmLambda "x"
                  (TmIndType "nat" [])
                  (TmLambda "y"
                    (TmIndType "nat" [])
                    (TmLambda ".0"
                      (TmIndType "le" [TmRel "x" 1, TmRel "y" 0])
                      (TmConstr "leS" [TmRel "x" 2, TmRel "y" 1, TmRel ".0" 0]))))])
      `shouldBe` True
    it "btree-yes" $
      isPositive natContext
      (Ind "btree" 1
            (TmProd "x"
              TmType
              TmType)
            (TmLambda "x"
              TmType
              (TmIndType "btree" [TmRel "x" 0]))
            [ ( "leaf"
              , TmProd "x"
                  TmType
                  (TmProd "_"
                    (TmRel "x" 0)
                    (TmIndType "btree" [TmRel "x" 1]))
              , TmLambda "x"
                  TmType
                  (TmLambda ".0"
                    (TmRel "x" 0)
                    (TmConstr "leaf" [TmRel "x" 1, TmRel ".0" 0 ])))
            , ( "node"
              , TmProd "x"
                TmType
                ( TmProd "_"
                  ( TmRel "x" 0 )
                  ( TmProd "_"
                    ( TmIndType "btree" [TmRel "x" 1] )
                    ( TmProd "_"
                      ( TmIndType "btree" [TmRel "x" 2] )
                      ( TmIndType "btree" [TmRel "x" 3] ))))
              , TmLambda "x"
                TmType
                ( TmLambda ".0"
                  ( TmRel "x" 0 )
                  ( TmLambda ".1"
                    ( TmIndType "btree" [TmRel "x" 1] )
                    ( TmLambda ".2"
                      ( TmIndType "btree" [TmRel "x" 2] )
                      ( TmConstr "node" [TmRel "x" 3, TmRel ".0" 2, TmRel ".1" 1, TmRel ".2" 0])))))])
      `shouldBe` True
    it "nattree-yes" $
      isPositive ilistContext
      ( Ind "nattree" 1
        ( TmProd "A"
            TmType
            TmType )
        ( TmLambda "A"
            TmType
          ( TmIndType "nattree"
            [ TmRel "A" 0 ]))
        [ ( "leaf"
          , TmProd "A"
              TmType
            ( TmIndType "nattree"
              [ TmRel "A" 0 ])
          , TmLambda "A"
              TmType
            ( TmConstr "leaf"
              [ TmRel "A" 0 ]))
        , ( "node"
          , TmProd "A"
              TmType
            ( TmProd "_"
              ( TmRel "A" 0 )
              ( TmProd "_"
                ( TmProd "_"
                  ( TmIndType "nat" [])
                  ( TmIndType "nattree"
                    [ TmRel "A" 2 ]))
                ( TmIndType "nattree"
                  [ TmRel "A" 2 ])))
          , TmLambda "A"
              TmType
            ( TmLambda ".0"
              ( TmRel "A" 0 )
              ( TmLambda ".1"
                ( TmProd "_"
                  ( TmIndType "nat" [])
                  ( TmIndType "nattree"
                    [ TmRel "A" 2 ]))
                ( TmConstr "node"
                  [ TmRel "A" 2
                  , TmRel ".0" 1
                  , TmRel ".1" 0 ]))))])
      `shouldBe` True
    it "yes-1" $
      isPositive ilistContext
      ( Ind "a" 1
        ( TmProd "x"
            TmType
            TmType )
        ( TmLambda "x"
            TmType
          ( TmIndType "a"
            [ TmRel "x" 0 ]))
        [ ( "aa"
          , TmProd "x"
              TmType
            ( TmProd "_"
              ( TmIndType "a"
                [ TmIndType "nat" []])
              ( TmIndType "a"
                [ TmRel "x" 1 ]))
          , TmLambda "x"
              TmType
            ( TmLambda ".0"
              ( TmIndType "a"
                [ TmIndType "nat" []])
              ( TmConstr "aa"
                [ TmRel "x" 1
                , TmRel ".0" 0 ])))])
      `shouldBe` True
    it "no-1" $
      isPositive ilistContext
      ( Ind "a" 1
        ( TmProd "T"
            TmType
            TmType )
        ( TmLambda "T"
            TmType
          ( TmIndType "a"
            [ TmRel "T" 0 ]))
        [ ( "aa"
          , TmProd "T"
              TmType
            ( TmProd "_"
              ( TmIndType "a"
                [ TmIndType "a"
                  [ TmRel "T" 0 ]])
              ( TmIndType "a"
                [ TmRel "T" 1 ]))
          , TmLambda "T"
              TmType
            ( TmLambda ".0"
              ( TmIndType "a"
                [ TmIndType "a"
                  [ TmRel "T" 0 ]])
              ( TmConstr "aa"
                [ TmRel "T" 1
                , TmRel ".0" 0 ])))])
      `shouldBe` False
    it "no-2" $
      isPositive ilistContext
      ( Ind "a" 1
        ( TmProd "T"
            TmType
            TmType )
        ( TmLambda "T"
            TmType
          ( TmIndType "a"
            [ TmRel "T" 0 ]))
        [ ( "aa"
          , TmProd "T"
              TmType
            ( TmIndType "a"
              [ TmIndType "a"
                [ TmRel "T" 0 ]])
          , TmLambda "T"
              TmType
            ( TmConstr "aa"
              [ TmRel "T" 0 ]))])
      `shouldBe` False
    it "yes-2" $
      isPositive ilistContext
      ( Ind "a" 1
        ( TmProd "T"
            TmType
            TmType )
        ( TmLambda "T"
            TmType
          ( TmIndType "a"
            [ TmRel "T" 0 ]))
        [ ( "aa"
          , TmProd "T"
              TmType
            ( TmProd "_"
              ( TmProd "_"
                ( TmRel "T" 0 )
                ( TmIndType "a"
                  [ TmRel "T" 1 ]))
              ( TmIndType "a"
                [ TmRel "T" 1 ]))
          , TmLambda "T"
              TmType
            ( TmLambda ".0"
              ( TmProd "_"
                ( TmRel "T" 0 )
                ( TmIndType "a"
                  [ TmRel "T" 1 ]))
              ( TmConstr "aa"
                [ TmRel "T" 1
                , TmRel ".0" 0 ])))])
      `shouldBe` True
    it "yes-3" $
      isPositive ilistContext
      ( Ind "a" 1
        ( TmProd "T"
            TmType
            TmType )
        ( TmLambda "T"
            TmType
          ( TmIndType "a"
            [ TmRel "T" 0 ]))
        [ ( "aa"
          , TmProd "T"
              TmType
            ( TmProd "_"
              ( TmProd "_"
                ( TmRel "T" 0 )
                ( TmProd "_"
                  ( TmRel "T" 1 )
                  ( TmIndType "a"
                    [ TmRel "T" 2 ])))
              ( TmIndType "a"
                [ TmRel "T" 1 ]))
          , TmLambda "T"
              TmType
            ( TmLambda ".0"
              ( TmProd "_"
                ( TmRel "T" 0 )
                ( TmProd "_"
                  ( TmRel "T" 1 )
                  ( TmIndType "a"
                    [ TmRel "T" 2 ])))
              ( TmConstr "aa"
                [ TmRel "T" 1
                , TmRel ".0" 0 ])))])
      `shouldBe` True
    it "no-3" $
      isPositive ilistContext
      ( Ind "a" 1
        ( TmProd "T"
            TmType
            TmType )
        ( TmLambda "T"
            TmType
          ( TmIndType "a"
            [ TmRel "T" 0 ]))
        [ ( "aa"
          , TmProd "T"
              TmType
            ( TmProd "_"
              ( TmProd "_"
                ( TmRel "T" 0 )
                ( TmProd "_"
                  ( TmIndType "a"
                    [ TmRel "T" 1 ])
                  ( TmIndType "a"
                    [ TmRel "T" 2 ])))
              ( TmIndType "a"
                [ TmRel "T" 1 ]))
          , TmLambda "T"
              TmType
            ( TmLambda ".0"
              ( TmProd "_"
                ( TmRel "T" 0 )
                ( TmProd "_"
                  ( TmIndType "a"
                    [ TmRel "T" 1 ])
                  ( TmIndType "a"
                    [ TmRel "T" 2 ])))
              ( TmConstr "aa"
                [ TmRel "T" 1
                , TmRel ".0" 0 ])))])
      `shouldBe` False
    it "yes-4" $
      isPositive ilistContext
      ( Ind "a" 1
        ( TmProd "T"
            TmType
            TmType )
        ( TmLambda "T"
            TmType
          ( TmIndType "a"
            [ TmRel "T" 0 ]))
        [ ( "aa"
          , TmProd "T"
              TmType
            ( TmProd "_"
              ( TmAppl
                [ TmLambda "T"
                    TmType
                  ( TmLambda ".0"
                    ( TmIndType "nat" [])
                    ( TmIndType "ilist"
                      [ TmRel "T" 1
                      , TmRel ".0" 0 ]))
                , TmIndType "a"
                  [ TmRel "T" 0 ]
                , TmConstr "O" []])
              ( TmIndType "a"
                [ TmRel "T" 1 ]))
          , TmLambda "T"
              TmType
            ( TmLambda ".0"
              ( TmAppl
                [ TmLambda "T"
                    TmType
                  ( TmLambda ".0"
                    ( TmIndType "nat" [])
                    ( TmIndType "ilist"
                      [ TmRel "T" 1
                      , TmRel ".0" 0 ]))
                , TmIndType "a"
                  [ TmRel "T" 0 ]
                , TmConstr "O" []])
              ( TmConstr "aa"
                [ TmRel "T" 1
                , TmRel ".0" 0 ])))])
      `shouldBe` True
    it "nested-OK" $
      isPositive nestedPosContext
      ( Ind "tok" 0
          TmType
        ( TmIndType "tok" [])
        [ ( "tok1"
          , TmProd "_"
            ( TmAppl
              [ TmLambda "T"
                  TmType
                ( TmLambda ".0"
                    TmType
                  ( TmIndType "t2"
                    [ TmRel "T" 1
                    , TmRel ".0" 0 ]))
              , TmIndType "tok" []
              , TmIndType "nat" []])
            ( TmIndType "tok" [])
          , TmLambda ".0"
            ( TmAppl
              [ TmLambda "T"
                  TmType
                ( TmLambda ".0"
                    TmType
                  ( TmIndType "t2"
                    [ TmRel "T" 1
                    , TmRel ".0" 0 ]))
              , TmIndType "tok" []
              , TmIndType "nat" []])
            ( TmConstr "tok1"
              [ TmRel ".0" 0 ]))])
      `shouldBe` True
    it "nested-FAIL" $
      isPositive nestedPosContext
      ( Ind "tfail" 0
          TmType
        ( TmIndType "tfail" [])
        [ ( "tfail1"
          , TmProd "_"
            ( TmAppl
              [ TmLambda "T"
                  TmType
                ( TmLambda ".0"
                    TmType
                  ( TmIndType "t1"
                    [ TmRel "T" 1
                    , TmRel ".0" 0 ]))
              , TmIndType "tfail" []
              , TmIndType "nat" []])
            ( TmIndType "tfail" [])
          , TmLambda ".0"
            ( TmAppl
              [ TmLambda "T"
                  TmType
                ( TmLambda ".0"
                    TmType
                  ( TmIndType "t1"
                    [ TmRel "T" 1
                    , TmRel ".0" 0 ]))
              , TmIndType "tfail" []
              , TmIndType "nat" []])
            ( TmConstr "tfail1"
              [ TmRel ".0" 0 ]))])
      `shouldBe` False
