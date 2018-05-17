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
