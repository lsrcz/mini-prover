module MiniProver.Core.RenameSpec (main, spec) where

import Test.Hspec
import MiniProver.Core.Syntax
import MiniProver.Core.Rename
import MiniProver.Utils.ContextForTesting

main :: IO ()
main = hspec spec

spec :: Spec
spec =
  describe "renameInd" $ do
    it "nat" $
      renameInd []
      ( Ind "nat" 0
          TmType
        ( TmIndType "nat" [])
        [ ( "O"
          , TmIndType "nat" []
          , TmConstr "O" [])
        , ( "S"
          , TmProd "_"
            ( TmIndType "nat" [])
            ( TmIndType "nat" [])
          , TmLambda ".0"
            ( TmIndType "nat" [])
            ( TmConstr "S"
              [ TmRel ".0" 0 ]))])
      `shouldBe`
      Ind "nat" 0
        TmType
      ( TmIndType "nat" [])
      [ ( "O"
        , TmIndType "nat" []
        , TmConstr "O" [])
      , ( "S"
        , TmProd "_"
          ( TmIndType "nat" [])
          ( TmIndType "nat" [])
        , TmLambda "n"
          ( TmIndType "nat" [])
          ( TmConstr "S"
            [ TmRel "n" 0 ]))]
    it "ilist" $
      renameInd realNatContext
      ( Ind "ilist" 1
        ( TmProd "T"
            TmType
          ( TmProd "_"
            ( TmIndType "nat" [])
              TmType ))
        ( TmLambda "T"
            TmType
          ( TmLambda ".0"
            ( TmIndType "nat" [])
            ( TmIndType "ilist"
              [ TmRel "T" 1
              , TmRel ".0" 0 ])))
        [ ( "inil"
          , TmProd "T"
              TmType
            ( TmIndType "ilist"
              [ TmRel "T" 0
              , TmConstr "O" []])
          , TmLambda "T"
              TmType
            ( TmConstr "inil"
              [ TmRel "T" 0 ]))
        , ( "icons"
          , TmProd "T"
              TmType
            ( TmProd "n"
              ( TmIndType "nat" [])
              ( TmProd "_"
                ( TmRel "T" 1 )
                ( TmProd "_"
                  ( TmIndType "ilist"
                    [ TmRel "T" 2
                    , TmRel "n" 1 ])
                  ( TmIndType "ilist"
                    [ TmRel "T" 3
                    , TmConstr "S"
                      [ TmRel "n" 2 ]]))))
          , TmLambda "T"
              TmType
            ( TmLambda "n"
              ( TmIndType "nat" [])
              ( TmLambda ".0"
                ( TmRel "T" 1 )
                ( TmLambda ".1"
                  ( TmIndType "ilist"
                    [ TmRel "T" 2
                    , TmRel "n" 1 ])
                  ( TmConstr "icons"
                    [ TmRel "T" 3
                    , TmRel "n" 2
                    , TmRel ".0" 1
                    , TmRel ".1" 0 ])))))])
      `shouldBe`
      Ind "ilist" 1
        ( TmProd "T"
            TmType
          ( TmProd "_"
            ( TmIndType "nat" [])
              TmType ))
        ( TmLambda "T"
            TmType
          ( TmLambda "n"
            ( TmIndType "nat" [])
            ( TmIndType "ilist"
              [ TmRel "T" 1
              , TmRel "n" 0 ])))
        [ ( "inil"
          , TmProd "T"
              TmType
            ( TmIndType "ilist"
              [ TmRel "T" 0
              , TmConstr "O" []])
          , TmLambda "T"
              TmType
            ( TmConstr "inil"
              [ TmRel "T" 0 ]))
        , ( "icons"
          , TmProd "T"
              TmType
            ( TmProd "n"
              ( TmIndType "nat" [])
              ( TmProd "_"
                ( TmRel "T" 1 )
                ( TmProd "_"
                  ( TmIndType "ilist"
                    [ TmRel "T" 2
                    , TmRel "n" 1 ])
                  ( TmIndType "ilist"
                    [ TmRel "T" 3
                    , TmConstr "S"
                      [ TmRel "n" 2 ]]))))
          , TmLambda "T"
              TmType
            ( TmLambda "n"
              ( TmIndType "nat" [])
              ( TmLambda "t"
                ( TmRel "T" 1 )
                ( TmLambda "i"
                  ( TmIndType "ilist"
                    [ TmRel "T" 2
                    , TmRel "n" 1 ])
                  ( TmConstr "icons"
                    [ TmRel "T" 3
                    , TmRel "n" 2
                    , TmRel "t" 1
                    , TmRel "i" 0 ])))))]