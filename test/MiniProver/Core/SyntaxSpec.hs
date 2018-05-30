module MiniProver.Core.SyntaxSpec (main,spec) where

import Test.Hspec
import MiniProver.Core.Syntax

main :: IO ()
main = hspec spec

spec :: Spec
spec =
  describe "termmEqNameless" $ do
    it "all in one" $
      termEqNameless
      ( TmLambda "T"
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
                            , "y"
                            , "i0" ]
                            ( TmAppl
                              [ TmRel "f0" 6
                              , TmRel "n0" 2
                              , TmRel "y" 1
                              , TmRel "i0" 0
                              , TmAppl
                                [ TmRel "F" 5
                                , TmRel "n0" 2
                                , TmRel "i0" 0 ]])])))))))))
      ( TmLambda "1"
            TmType
          ( TmLambda "2"
            ( TmProd "3"
              ( TmIndType "nat" [])
              ( TmProd "4"
                ( TmIndType "ilist"
                  [ TmRel "5" 1
                  , TmRel "6" 0 ])
                  TmType ))
            ( TmLambda "7"
              ( TmAppl
                [ TmRel "8" 0
                , TmConstr "O" []
                , TmConstr "inil"
                  [ TmRel "9" 1 ]])
              ( TmLambda "10"
                ( TmProd "11"
                  ( TmIndType "nat" [])
                  ( TmProd "12"
                    ( TmRel "13" 3 )
                    ( TmProd "14"
                      ( TmIndType "ilist"
                        [ TmRel "15" 4
                        , TmRel "16" 1 ])
                      ( TmProd "17"
                        ( TmAppl
                          [ TmRel "18" 4
                          , TmRel "19" 2
                          , TmRel "20" 0 ])
                        ( TmAppl
                          [ TmRel "21" 5
                          , TmConstr "S"
                            [ TmRel "22" 3 ]
                          , TmConstr "icons"
                            [ TmRel "23" 6
                            , TmRel "24" 3
                            , TmRel "25" 2
                            , TmRel "26" 1 ]])))))
                ( TmFix 2
                  ( TmLambda "27"
                    ( TmProd "28"
                      ( TmIndType "nat" [])
                      ( TmProd "29"
                        ( TmIndType "ilist"
                          [ TmRel "30" 4
                          , TmRel "31" 0 ])
                        ( TmAppl
                          [ TmRel "32" 4
                          , TmRel "33" 1
                          , TmRel "34" 0 ])))
                    ( TmLambda "35"
                      ( TmIndType "nat" [])
                      ( TmLambda "36"
                        ( TmIndType "ilist"
                          [ TmRel "37" 5
                          , TmRel "38" 0 ])
                        ( TmMatch 1
                          ( TmRel "39" 0 )
                            "40"
                          [ "ilist"
                          , "_"
                          , "41" ]
                          ( TmAppl
                            [ TmRel "42" 7
                            , TmRel "43" 1
                            , TmRel "44" 0 ])
                          [ Equation
                            [ "inil"
                            , "_" ]
                            ( TmRel "45" 4 )
                          , Equation
                            [ "icons"
                            , "_"
                            , "46"
                            , "47"
                            , "48" ]
                            ( TmAppl
                              [ TmRel "49" 6
                              , TmRel "50" 2
                              , TmRel "51" 1
                              , TmRel "52" 0
                              , TmAppl
                                [ TmRel "53" 5
                                , TmRel "54" 2
                                , TmRel "55" 0 ]])])))))))))
      `shouldBe` True
    it "all in one" $
      termEqNameless
      ( TmLambda "T"
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
                            , "y"
                            , "i0" ]
                            ( TmAppl
                              [ TmRel "f0" 6
                              , TmRel "n0" 2
                              , TmRel "y" 1
                              , TmRel "i0" 0
                              , TmAppl
                                [ TmRel "F" 5
                                , TmRel "n0" 2
                                , TmRel "i0" 0 ]])])))))))))
      ( TmLambda "1"
            TmType
          ( TmLambda "2"
            ( TmProd "3"
              ( TmIndType "nat" [])
              ( TmProd "4"
                ( TmIndType "ilist"
                  [ TmRel "5" 1
                  , TmRel "6" 0 ])
                  TmType ))
            ( TmLambda "7"
              ( TmAppl
                [ TmRel "8" 0
                , TmConstr "O" []
                , TmConstr "inil"
                  [ TmRel "9" 1 ]])
              ( TmLambda "10"
                ( TmProd "11"
                  ( TmIndType "nat" [])
                  ( TmProd "12"
                    ( TmRel "13" 3 )
                    ( TmProd "14"
                      ( TmIndType "ilist"
                        [ TmRel "15" 4
                        , TmRel "16" 1 ])
                      ( TmProd "17"
                        ( TmAppl
                          [ TmRel "18" 4
                          , TmRel "19" 2
                          , TmRel "20" 0 ])
                        ( TmAppl
                          [ TmRel "21" 5
                          , TmConstr "S"
                            [ TmRel "22" 3 ]
                          , TmConstr "icons"
                            [ TmRel "23" 6
                            , TmRel "24" 3
                            , TmRel "25" 2
                            , TmRel "26" 1 ]])))))
                ( TmFix 2
                  ( TmLambda "27"
                    ( TmProd "28"
                      ( TmIndType "nat" [])
                      ( TmProd "29"
                        ( TmIndType "ilist"
                          [ TmRel "30" 4
                          , TmRel "31" 0 ])
                        ( TmAppl
                          [ TmRel "32" 4
                          , TmRel "33" 1
                          , TmRel "34" 0 ])))
                    ( TmLambda "35"
                      ( TmIndType "nat" [])
                      ( TmLambda "36"
                        ( TmIndType "ilist"
                          [ TmRel "37" 5
                          , TmRel "38" 0 ])
                        ( TmMatch 1
                          ( TmRel "39" 0 )
                            "40"
                          [ "ilist"
                          , "_"
                          , "41" ]
                          ( TmAppl
                            [ TmRel "42" 7
                            , TmRel "43" 1
                            , TmRel "44" 0 ])
                          [ Equation
                            [ "inil"
                            , "_" ]
                            ( TmRel "45" 4 )
                          , Equation
                            [ "icons"
                            , "_"
                            , "46"
                            , "47"
                            , "48" ]
                            ( TmAppl
                              [ TmRel "49" 6
                              , TmRel "50" 2
                              , TmRel "51" 1
                              , TmRel "52" 0
                              , TmAppl
                                [ TmRel "53" 5
                                , TmRel "54" 2
                                , TmRel "55" 1 ]])])))))))))
      `shouldBe` False