module MiniProver.Core.RenameSpec (main, spec) where

import Test.Hspec
import MiniProver.Core.Syntax
import MiniProver.Core.Rename
import MiniProver.Utils.ContextForTesting

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
  describe "renameTerm" $
    it "ilist_ind" $
      renameTerm (tail realIlistContext)
      ( TmLambda "T"
            TmType
          ( TmLambda ".P"
            ( TmProd "n"
              ( TmIndType "nat" [])
              ( TmProd "_"
                ( TmIndType "ilist"
                  [ TmRel "T" 1
                  , TmRel "n" 0 ])
                  TmType ))
            ( TmLambda ".f"
              ( TmAppl
                [ TmRel "P" 0
                , TmConstr "O" []
                , TmConstr "inil"
                  [ TmRel "T" 1 ]])
              ( TmLambda ".f0"
                ( TmProd "n"
                  ( TmIndType "nat" [])
                  ( TmProd "t"
                    ( TmRel "T" 3 )
                    ( TmProd "i"
                      ( TmIndType "ilist"
                        [ TmRel "T" 4
                        , TmRel "n" 1 ])
                      ( TmProd "_"
                        ( TmAppl
                          [ TmRel ".P" 4
                          , TmRel "n" 2
                          , TmRel "i" 0 ])
                        ( TmAppl
                          [ TmRel ".P" 5
                          , TmConstr "S"
                            [ TmRel "n" 3 ]
                          , TmConstr "icons"
                            [ TmRel "T" 6
                            , TmRel "n" 3
                            , TmRel "t" 2
                            , TmRel "i" 1 ]])))))
                ( TmFix 2
                  ( TmLambda ".F"
                    ( TmProd "n"
                      ( TmIndType "nat" [])
                      ( TmProd "."
                        ( TmIndType "ilist"
                          [ TmRel "T" 4
                          , TmRel "n" 0 ])
                        ( TmAppl
                          [ TmRel ".P" 4
                          , TmRel "n" 1
                          , TmRel "." 0 ])))
                    ( TmLambda "n"
                      ( TmIndType "nat" [])
                      ( TmLambda "."
                        ( TmIndType "ilist"
                          [ TmRel "T" 5
                          , TmRel "n" 0 ])
                        ( TmMatch 1
                          ( TmRel "." 0 )
                            "."
                          [ "ilist"
                          , "_"
                          , ".n" ]
                          ( TmAppl
                            [ TmRel "P" 7
                            , TmRel ".n" 1
                            , TmRel "." 0 ])
                          [ Equation
                            [ "inil"
                            , "_" ]
                            ( TmRel ".f" 4 )
                          , Equation
                            [ "icons"
                            , "_"
                            , ".n"
                            , ".t"
                            , ".i" ]
                            ( TmAppl
                              [ TmRel ".f" 6
                              , TmRel ".n" 2
                              , TmRel ".t" 1
                              , TmRel ".i" 0
                              , TmAppl
                                [ TmRel ".F" 5
                                , TmRel ".n" 2
                                , TmRel ".i" 0 ]])])))))))))
        `shouldBe`
        TmLambda "T"
            TmType
          ( TmLambda "P"
            ( TmProd "n"
              ( TmIndType "nat" [])
              ( TmProd "_"
                ( TmIndType "ilist"
                  [ TmRel "T" 1
                  , TmRel "n" 0 ])
                  TmType ))
            ( TmLambda "f"
              ( TmAppl
                [ TmRel "P" 0
                , TmConstr "O" []
                , TmConstr "inil"
                  [ TmRel "T" 1 ]])
              ( TmLambda "f0"
                ( TmProd "n"
                  ( TmIndType "nat" [])
                  ( TmProd "t"
                    ( TmRel "T" 3 )
                    ( TmProd "i"
                      ( TmIndType "ilist"
                        [ TmRel "T" 4
                        , TmRel "n" 1 ])
                      ( TmProd "_"
                        ( TmAppl
                          [ TmRel "P" 4
                          , TmRel "n" 2
                          , TmRel "i" 0 ])
                        ( TmAppl
                          [ TmRel "P" 5
                          , TmConstr "S"
                            [ TmRel "n" 3 ]
                          , TmConstr "icons"
                            [ TmRel "T" 6
                            , TmRel "n" 3
                            , TmRel "t" 2
                            , TmRel "i" 1 ]])))))
                ( TmFix 2
                  ( TmLambda "F"
                    ( TmProd "n"
                      ( TmIndType "nat" [])
                      ( TmProd "i"
                        ( TmIndType "ilist"
                          [ TmRel "T" 4
                          , TmRel "n" 0 ])
                        ( TmAppl
                          [ TmRel "P" 4
                          , TmRel "n" 1
                          , TmRel "i" 0 ])))
                    ( TmLambda "n"
                      ( TmIndType "nat" [])
                      ( TmLambda "i"
                        ( TmIndType "ilist"
                          [ TmRel "T" 5
                          , TmRel "n" 0 ])
                        ( TmMatch 1
                          ( TmRel "i" 0 )
                            "i0"
                          [ "ilist"
                          , "_"
                          , "n0" ]
                          ( TmAppl
                            [ TmRel "P" 7
                            , TmRel "n0" 1
                            , TmRel "i0" 0 ])
                          [ Equation
                            [ "inil"
                            , "_" ]
                            ( TmRel "f" 4 )
                          , Equation
                            [ "icons"
                            , "_"
                            , "n0"
                            , "t"
                            , "i0" ]
                            ( TmAppl
                              [ TmRel "f0" 6
                              , TmRel "n0" 2
                              , TmRel "t" 1
                              , TmRel "i0" 0
                              , TmAppl
                                [ TmRel "F" 5
                                , TmRel "n0" 2
                                , TmRel "i0" 0 ]])]))))))))
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