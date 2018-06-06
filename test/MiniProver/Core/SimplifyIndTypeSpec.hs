module MiniProver.Core.SimplifyIndTypeSpec (main, spec) where

import Test.Hspec
import MiniProver.Core.Syntax
import MiniProver.Core.SimplifyIndType
import MiniProver.Utils.ContextForTesting

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
  describe "simplifyIndType" $ do
    it "ty eq_ind" $
      simplifyIndType
      ( TmProd "T"
          TmType
        ( TmProd "x"
          ( TmRel "T" 0 )
          ( TmProd "P"
            ( TmProd "t"
              ( TmRel "T" 1 )
              ( TmProd "_"
                ( TmAppl
                  [ TmLambda "T"
                      TmType
                    ( TmLambda "x"
                      ( TmRel "T" 0 )
                      ( TmLambda ".0"
                        ( TmRel "T" 1 )
                        ( TmIndType "eq"
                          [ TmRel "T" 2
                          , TmRel "x" 1
                          , TmRel ".0" 0 ])))
                  , TmRel "T" 2
                  , TmRel "x" 1
                  , TmRel "t" 0 ])
                  TmType ))
            ( TmProd "f"
              ( TmAppl
                [ TmRel "P" 0
                , TmRel "x" 1
                , TmAppl
                  [ TmLambda "T"
                      TmType
                    ( TmLambda "x"
                      ( TmRel "T" 0 )
                      ( TmConstr "eq_refl"
                        [ TmRel "T" 1
                        , TmRel "x" 0 ]))
                  , TmRel "T" 2
                  , TmRel "x" 1 ]])
              ( TmProd "y"
                ( TmRel "T" 3 )
                ( TmProd "e"
                  ( TmAppl
                    [ TmLambda "T"
                        TmType
                      ( TmLambda "x"
                        ( TmRel "T" 0 )
                        ( TmLambda ".0"
                          ( TmRel "T" 1 )
                          ( TmIndType "eq"
                            [ TmRel "T" 2
                            , TmRel "x" 1
                            , TmRel ".0" 0 ])))
                    , TmRel "T" 4
                    , TmRel "x" 3
                    , TmRel "y" 0 ])
                  ( TmAppl
                    [ TmRel "P" 3
                    , TmRel "y" 1
                    , TmRel "e" 0 ])))))))
      `shouldBe`
      TmProd "T"
        TmType
      ( TmProd "x"
        ( TmRel "T" 0 )
        ( TmProd "P"
          ( TmProd "t"
            ( TmRel "T" 1 )
            ( TmProd "_"
              ( TmIndType "eq"
                [ TmRel "T" 2
                , TmRel "x" 1
                , TmRel "t" 0 ])
                TmType ))
          ( TmProd "f"
            ( TmAppl
              [ TmRel "P" 0
              , TmRel "x" 1
              , TmConstr "eq_refl"
                [ TmRel "T" 2
                , TmRel "x" 1 ]])
            ( TmProd "y"
              ( TmRel "T" 3 )
              ( TmProd "e"
                ( TmIndType "eq"
                  [ TmRel "T" 4
                  , TmRel "x" 3
                  , TmRel "y" 0 ])
                ( TmAppl
                  [ TmRel "P" 3
                  , TmRel "y" 1
                  , TmRel "e" 0 ]))))))
    it "tm eq_ind" $
      simplifyIndType
      ( TmLambda "T"
          TmType
        ( TmLambda "x"
          ( TmRel "T" 0 )
          ( TmLambda "P"
            ( TmProd "t"
              ( TmRel "T" 1 )
              ( TmProd "_"
                ( TmAppl
                  [ TmLambda "T"
                      TmType
                    ( TmLambda "x"
                      ( TmRel "T" 0 )
                      ( TmLambda ".0"
                        ( TmRel "T" 1 )
                        ( TmIndType "eq"
                          [ TmRel "T" 2
                          , TmRel "x" 1
                          , TmRel ".0" 0 ])))
                  , TmRel "T" 2
                  , TmRel "x" 1
                  , TmRel "t" 0 ])
                  TmType ))
            ( TmLambda "f"
              ( TmAppl
                [ TmRel "P" 0
                , TmRel "x" 1
                , TmAppl
                  [ TmLambda "T"
                      TmType
                    ( TmLambda "x"
                      ( TmRel "T" 0 )
                      ( TmConstr "eq_refl"
                        [ TmRel "T" 1
                        , TmRel "x" 0 ]))
                  , TmRel "T" 2
                  , TmRel "x" 1 ]])
              ( TmLambda "y"
                ( TmRel "T" 3 )
                ( TmLambda "e"
                  ( TmAppl
                    [ TmLambda "T"
                        TmType
                      ( TmLambda "x"
                        ( TmRel "T" 0 )
                        ( TmLambda ".0"
                          ( TmRel "T" 1 )
                          ( TmIndType "eq"
                            [ TmRel "T" 2
                            , TmRel "x" 1
                            , TmRel ".0" 0 ])))
                    , TmRel "T" 4
                    , TmRel "x" 3
                    , TmRel "y" 0 ])
                  ( TmMatch 2
                    ( TmRel "e" 0 )
                      "e0"
                    [ "eq"
                    , "_"
                    , "_"
                    , "y0" ]
                    ( TmAppl
                      [ TmRel "P" 5
                      , TmRel "y0" 1
                      , TmRel "e0" 0 ])
                    [ Equation
                      [ "eq_refl"
                      , "_"
                      , "_" ]
                      ( TmRel "f" 2 )])))))))
      `shouldBe`
        TmLambda "T"
          TmType
        ( TmLambda "x"
          ( TmRel "T" 0 )
          ( TmLambda "P"
            ( TmProd "t"
              ( TmRel "T" 1 )
              ( TmProd "_"
                ( TmIndType "eq"
                  [ TmRel "T" 2
                  , TmRel "x" 1
                  , TmRel "t" 0 ])
                  TmType ))
            ( TmLambda "f"
              ( TmAppl
                [ TmRel "P" 0
                , TmRel "x" 1
                , TmConstr "eq_refl"
                  [ TmRel "T" 2
                  , TmRel "x" 1 ]])
              ( TmLambda "y"
                ( TmRel "T" 3 )
                ( TmLambda "e"
                  ( TmIndType "eq"
                    [ TmRel "T" 4
                    , TmRel "x" 3
                    , TmRel "y" 0 ])
                  ( TmMatch 2
                    ( TmRel "e" 0 )
                      "e0"
                    [ "eq"
                    , "_"
                    , "_"
                    , "y0" ]
                    ( TmAppl
                      [ TmRel "P" 5
                      , TmRel "y0" 1
                      , TmRel "e0" 0 ])
                    [ Equation
                      [ "eq_refl"
                      , "_"
                      , "_" ]
                      ( TmRel "f" 2 )]))))))
    it "ty and_ind" $
      simplifyIndType
      ( TmProd "A"
          TmType
        ( TmProd "B"
            TmType
          ( TmProd "P"
            ( TmProd "_"
              ( TmAppl
                [ TmLambda "A"
                    TmType
                  ( TmLambda "B"
                      TmType
                    ( TmIndType "and"
                      [ TmRel "A" 1
                      , TmRel "B" 0 ]))
                , TmRel "A" 1
                , TmRel "B" 0 ])
                TmType )
            ( TmProd "f"
              ( TmProd "a"
                ( TmRel "A" 2 )
                ( TmProd "b"
                  ( TmRel "B" 2 )
                  ( TmAppl
                    [ TmRel "P" 2
                    , TmAppl
                      [ TmLambda "A"
                          TmType
                        ( TmLambda "B"
                            TmType
                          ( TmLambda ".0"
                            ( TmRel "A" 1 )
                            ( TmLambda ".1"
                              ( TmRel "B" 1 )
                              ( TmConstr "conj"
                                [ TmRel "A" 3
                                , TmRel "B" 2
                                , TmRel ".0" 1
                                , TmRel ".1" 0 ]))))
                      , TmRel "A" 4
                      , TmRel "B" 3
                      , TmRel "a" 1
                      , TmRel "b" 0 ]])))
              ( TmProd "a"
                ( TmAppl
                  [ TmLambda "A"
                      TmType
                    ( TmLambda "B"
                        TmType
                      ( TmIndType "and"
                        [ TmRel "A" 1
                        , TmRel "B" 0 ]))
                  , TmRel "A" 3
                  , TmRel "B" 2 ])
                ( TmAppl
                  [ TmRel "P" 2
                  , TmRel "a" 0 ]))))))
      `shouldBe`
      TmProd "A"
          TmType
        ( TmProd "B"
            TmType
          ( TmProd "P"
            ( TmProd "_"
              ( TmIndType "and"
                [ TmRel "A" 1
                , TmRel "B" 0 ])
                TmType )
            ( TmProd "f"
              ( TmProd "a"
                ( TmRel "A" 2 )
                ( TmProd "b"
                  ( TmRel "B" 2 )
                  ( TmAppl
                    [ TmRel "P" 2
                    , TmConstr "conj"
                      [ TmRel "A" 4
                      , TmRel "B" 3
                      , TmRel "a" 1
                      , TmRel "b" 0 ]])))
              ( TmProd "a"
                ( TmIndType "and"
                  [ TmRel "A" 3
                  , TmRel "B" 2 ])
                ( TmAppl
                  [ TmRel "P" 2
                  , TmRel "a" 0 ])))))
    it "tm and_ind" $
      simplifyIndType
      ( TmLambda "A"
            TmType
          ( TmLambda "B"
              TmType
            ( TmLambda "P"
              ( TmProd "_"
                ( TmAppl
                  [ TmLambda "A"
                      TmType
                    ( TmLambda "B"
                        TmType
                      ( TmIndType "and"
                        [ TmRel "A" 1
                        , TmRel "B" 0 ]))
                  , TmRel "A" 1
                  , TmRel "B" 0 ])
                  TmType )
              ( TmLambda "f"
                ( TmProd "a"
                  ( TmRel "A" 2 )
                  ( TmProd "b"
                    ( TmRel "B" 2 )
                    ( TmAppl
                      [ TmRel "P" 2
                      , TmAppl
                        [ TmLambda "A"
                            TmType
                          ( TmLambda "B"
                              TmType
                            ( TmLambda ".0"
                              ( TmRel "A" 1 )
                              ( TmLambda ".1"
                                ( TmRel "B" 1 )
                                ( TmConstr "conj"
                                  [ TmRel "A" 3
                                  , TmRel "B" 2
                                  , TmRel ".0" 1
                                  , TmRel ".1" 0 ]))))
                        , TmRel "A" 4
                        , TmRel "B" 3
                        , TmRel "a" 1
                        , TmRel "b" 0 ]])))
                ( TmLambda "a"
                  ( TmAppl
                    [ TmLambda "A"
                        TmType
                      ( TmLambda "B"
                          TmType
                        ( TmIndType "and"
                          [ TmRel "A" 1
                          , TmRel "B" 0 ]))
                    , TmRel "A" 3
                    , TmRel "B" 2 ])
                  ( TmMatch 2
                    ( TmRel "a" 0 )
                      "a0"
                    [ "and"
                    , "_"
                    , "_" ]
                    ( TmAppl
                      [ TmRel "P" 3
                      , TmRel "a0" 0 ])
                    [ Equation
                      [ "conj"
                      , "_"
                      , "_"
                      , "x"
                      , "x0" ]
                      ( TmAppl
                        [ TmRel "f" 3
                        , TmRel "x" 1
                        , TmRel "x0" 0 ])]))))))
      `shouldBe`
      TmLambda "A"
            TmType
          ( TmLambda "B"
              TmType
            ( TmLambda "P"
              ( TmProd "_"
                ( TmIndType "and"
                  [ TmRel "A" 1
                  , TmRel "B" 0 ])
                  TmType )
              ( TmLambda "f"
                ( TmProd "a"
                  ( TmRel "A" 2 )
                  ( TmProd "b"
                    ( TmRel "B" 2 )
                    ( TmAppl
                      [ TmRel "P" 2
                      , TmConstr "conj"
                        [ TmRel "A" 4
                        , TmRel "B" 3
                        , TmRel "a" 1
                        , TmRel "b" 0 ]])))
                ( TmLambda "a"
                  ( TmIndType "and"
                    [ TmRel "A" 3
                    , TmRel "B" 2 ])
                  ( TmMatch 2
                    ( TmRel "a" 0 )
                      "a0"
                    [ "and"
                    , "_"
                    , "_" ]
                    ( TmAppl
                      [ TmRel "P" 3
                      , TmRel "a0" 0 ])
                    [ Equation
                      [ "conj"
                      , "_"
                      , "_"
                      , "x"
                      , "x0" ]
                      ( TmAppl
                        [ TmRel "f" 3
                        , TmRel "x" 1
                        , TmRel "x0" 0 ])])))))
    it "ty or_ind" $
      simplifyIndType
      ( TmProd "A"
          TmType
        ( TmProd "B"
            TmType
          ( TmProd "P"
            ( TmProd "_"
              ( TmAppl
                [ TmLambda "A"
                    TmType
                  ( TmLambda "B"
                      TmType
                    ( TmIndType "or"
                      [ TmRel "A" 1
                      , TmRel "B" 0 ]))
                , TmRel "A" 1
                , TmRel "B" 0 ])
                TmType )
            ( TmProd "f"
              ( TmProd "a"
                ( TmRel "A" 2 )
                ( TmAppl
                  [ TmRel "P" 1
                  , TmAppl
                    [ TmLambda "A"
                        TmType
                      ( TmLambda "B"
                          TmType
                        ( TmLambda ".0"
                          ( TmRel "A" 1 )
                          ( TmConstr "or_introl"
                            [ TmRel "A" 2
                            , TmRel "B" 1
                            , TmRel ".0" 0 ])))
                    , TmRel "A" 3
                    , TmRel "B" 2
                    , TmRel "a" 0 ]]))
              ( TmProd "f0"
                ( TmProd "b"
                  ( TmRel "B" 2 )
                  ( TmAppl
                    [ TmRel "P" 2
                    , TmAppl
                      [ TmLambda "A"
                          TmType
                        ( TmLambda "B"
                            TmType
                          ( TmLambda ".0"
                            ( TmRel "B" 0 )
                            ( TmConstr "or_intror"
                              [ TmRel "A" 2
                              , TmRel "B" 1
                              , TmRel ".0" 0 ])))
                      , TmRel "A" 4
                      , TmRel "B" 3
                      , TmRel "b" 0 ]]))
                ( TmProd "o"
                  ( TmAppl
                    [ TmLambda "A"
                        TmType
                      ( TmLambda "B"
                          TmType
                        ( TmIndType "or"
                          [ TmRel "A" 1
                          , TmRel "B" 0 ]))
                    , TmRel "A" 4
                    , TmRel "B" 3 ])
                  ( TmAppl
                    [ TmRel "P" 3
                    , TmRel "o" 0 ])))))))
      `shouldBe`
      TmProd "A"
          TmType
        ( TmProd "B"
            TmType
          ( TmProd "P"
            ( TmProd "_"
              ( TmIndType "or"
                [ TmRel "A" 1
                , TmRel "B" 0 ])
                TmType )
            ( TmProd "f"
              ( TmProd "a"
                ( TmRel "A" 2 )
                ( TmAppl
                  [ TmRel "P" 1
                  , TmConstr "or_introl"
                    [ TmRel "A" 3
                    , TmRel "B" 2
                    , TmRel "a" 0 ]]))
              ( TmProd "f0"
                ( TmProd "b"
                  ( TmRel "B" 2 )
                  ( TmAppl
                    [ TmRel "P" 2
                    , TmConstr "or_intror"
                      [ TmRel "A" 4
                      , TmRel "B" 3
                      , TmRel "b" 0 ]]))
                ( TmProd "o"
                  ( TmIndType "or"
                    [ TmRel "A" 4
                    , TmRel "B" 3 ])
                  ( TmAppl
                    [ TmRel "P" 3
                    , TmRel "o" 0 ]))))))
    it "tm ilist_ind" $
      simplifyIndType
      ( TmLambda "T"
            TmType
          ( TmLambda "P"
            ( TmProd "n"
              ( TmIndType "nat" [])
              ( TmProd "_"
                ( TmAppl
                  [ TmLambda "T"
                      TmType
                    ( TmLambda ".0"
                      ( TmIndType "nat" [])
                      ( TmIndType "ilist"
                        [ TmRel "T" 1
                        , TmRel ".0" 0 ]))
                  , TmRel "T" 1
                  , TmRel "n" 0 ])
                  TmType ))
            ( TmLambda "f"
              ( TmAppl
                [ TmRel "P" 0
                , TmConstr "O" []
                , TmAppl
                  [ TmLambda "T"
                      TmType
                    ( TmConstr "inil"
                      [ TmRel "T" 0 ])
                  , TmRel "T" 1 ]])
              ( TmLambda "f0"
                ( TmProd "n"
                  ( TmIndType "nat" [])
                  ( TmProd "t"
                    ( TmRel "T" 3 )
                    ( TmProd "i"
                      ( TmAppl
                        [ TmLambda "T"
                            TmType
                          ( TmLambda ".0"
                            ( TmIndType "nat" [])
                            ( TmIndType "ilist"
                              [ TmRel "T" 1
                              , TmRel ".0" 0 ]))
                        , TmRel "T" 4
                        , TmRel "n" 1 ])
                      ( TmProd "_"
                        ( TmAppl
                          [ TmRel "P" 4
                          , TmRel "n" 2
                          , TmRel "i" 0 ])
                        ( TmAppl
                          [ TmRel "P" 5
                          , TmAppl
                            [ TmLambda ".0"
                              ( TmIndType "nat" [])
                              ( TmConstr "S"
                                [ TmRel ".0" 0 ])
                            , TmRel "n" 3 ]
                          , TmAppl
                            [ TmLambda "T"
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
                                      , TmRel ".1" 0 ]))))
                            , TmRel "T" 6
                            , TmRel "n" 3
                            , TmRel "t" 2
                            , TmRel "i" 1 ]])))))
                ( TmFix 2
                  ( TmLambda "F"
                    ( TmProd "n"
                      ( TmIndType "nat" [])
                      ( TmProd "i"
                        ( TmAppl
                          [ TmLambda "T"
                              TmType
                            ( TmLambda ".0"
                              ( TmIndType "nat" [])
                              ( TmIndType "ilist"
                                [ TmRel "T" 1
                                , TmRel ".0" 0 ]))
                          , TmRel "T" 4
                          , TmRel "n" 0 ])
                        ( TmAppl
                          [ TmRel "P" 4
                          , TmRel "n" 1
                          , TmRel "i" 0 ])))
                    ( TmLambda "n"
                      ( TmIndType "nat" [])
                      ( TmLambda "i"
                        ( TmAppl
                          [ TmLambda "T"
                              TmType
                            ( TmLambda ".0"
                              ( TmIndType "nat" [])
                              ( TmIndType "ilist"
                                [ TmRel "T" 1
                                , TmRel ".0" 0 ]))
                          , TmRel "T" 5
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
                                , TmRel "i0" 0 ]])]))))))))
  describe "simplifyIndCmd" $ do
    it "Ax" $
      simplifyIndCmd
      ( Ax "S_Sn"
        ( TmProd "n"
          ( TmIndType "nat" [])
          ( TmAppl
            [ TmLambda "T"
                TmType
              ( TmLambda "x"
                ( TmRel "T" 0 )
                ( TmLambda ".0"
                  ( TmRel "T" 1 )
                  ( TmIndType "eq"
                    [ TmRel "T" 2
                    , TmRel "x" 1
                    , TmRel ".0" 0 ])))
            , TmIndType "nat" []
            , TmRel "n" 0
            , TmAppl
              [ TmLambda ".0"
                ( TmIndType "nat" [])
                ( TmConstr "S"
                  [ TmRel ".0" 0 ])
              , TmRel "n" 0 ]])))
      `shouldBe`
      Ax "S_Sn"
        ( TmProd "n"
          ( TmIndType "nat" [])
          ( TmIndType "eq"
            [ TmIndType "nat" []
            , TmRel "n" 0
            , TmConstr "S"
              [ TmRel "n" 0 ]]))
    it "Def" $
      simplifyIndCmd
      ( Def "S_inj"
        ( TmProd "n"
          ( TmIndType "nat" [])
          ( TmProd "m"
            ( TmIndType "nat" [])
            ( TmProd "H"
              ( TmAppl
                [ TmLambda "T"
                    TmType
                  ( TmLambda "x"
                    ( TmRel "T" 0 )
                    ( TmLambda ".0"
                      ( TmRel "T" 1 )
                      ( TmIndType "eq"
                        [ TmRel "T" 2
                        , TmRel "x" 1
                        , TmRel ".0" 0 ])))
                , TmIndType "nat" []
                , TmRel "n" 1
                , TmRel "m" 0 ])
              ( TmAppl
                [ TmLambda "T"
                    TmType
                  ( TmLambda "x"
                    ( TmRel "T" 0 )
                    ( TmLambda ".0"
                      ( TmRel "T" 1 )
                      ( TmIndType "eq"
                        [ TmRel "T" 2
                        , TmRel "x" 1
                        , TmRel ".0" 0 ])))
                , TmIndType "nat" []
                , TmAppl
                  [ TmLambda ".0"
                    ( TmIndType "nat" [])
                    ( TmConstr "S"
                      [ TmRel ".0" 0 ])
                  , TmRel "n" 2 ]
                , TmAppl
                  [ TmLambda ".0"
                    ( TmIndType "nat" [])
                    ( TmConstr "S"
                      [ TmRel ".0" 0 ])
                  , TmRel "m" 1 ]]))))
        ( TmLambda "n"
          ( TmIndType "nat" [])
          ( TmLambda "m"
            ( TmIndType "nat" [])
            ( TmLambda "H"
              ( TmAppl
                [ TmLambda "T"
                    TmType
                  ( TmLambda "x"
                    ( TmRel "T" 0 )
                    ( TmLambda ".0"
                      ( TmRel "T" 1 )
                      ( TmIndType "eq"
                        [ TmRel "T" 2
                        , TmRel "x" 1
                        , TmRel ".0" 0 ])))
                , TmIndType "nat" []
                , TmRel "n" 1
                , TmRel "m" 0 ])
              ( TmMatch 2
                ( TmRel "H" 0 )
                  "H0"
                [ "eq"
                , "_"
                , "_"
                , "m0" ]
                ( TmAppl
                  [ TmLambda "T"
                      TmType
                    ( TmLambda "x"
                      ( TmRel "T" 0 )
                      ( TmLambda ".0"
                        ( TmRel "T" 1 )
                        ( TmIndType "eq"
                          [ TmRel "T" 2
                          , TmRel "x" 1
                          , TmRel ".0" 0 ])))
                  , TmIndType "nat" []
                  , TmAppl
                    [ TmLambda ".0"
                      ( TmIndType "nat" [])
                      ( TmConstr "S"
                        [ TmRel ".0" 0 ])
                    , TmRel "n" 4 ]
                  , TmAppl
                    [ TmLambda ".0"
                      ( TmIndType "nat" [])
                      ( TmConstr "S"
                        [ TmRel ".0" 0 ])
                    , TmRel "m0" 1 ]])
                [ Equation
                  [ "eq_refl"
                  , "_"
                  , "_" ]
                  ( TmAppl
                    [ TmLambda "T"
                        TmType
                      ( TmLambda "x"
                        ( TmRel "T" 0 )
                        ( TmConstr "eq_refl"
                          [ TmRel "T" 1
                          , TmRel "x" 0 ]))
                    , TmIndType "nat" []
                    , TmAppl
                      [ TmLambda ".0"
                        ( TmIndType "nat" [])
                        ( TmConstr "S"
                          [ TmRel ".0" 0 ])
                      , TmRel "n" 2 ]])])))))
      `shouldBe`
      Def "S_inj"
        ( TmProd "n"
          ( TmIndType "nat" [])
          ( TmProd "m"
            ( TmIndType "nat" [])
            ( TmProd "H"
              ( TmIndType "eq"
                [ TmIndType "nat" []
                , TmRel "n" 1
                , TmRel "m" 0 ])
              ( TmIndType "eq"
                [ TmIndType "nat" []
                , TmConstr "S"
                  [ TmRel "n" 2 ]
                , TmConstr "S"
                  [ TmRel "m" 1 ]]))))
        ( TmLambda "n"
          ( TmIndType "nat" [])
          ( TmLambda "m"
            ( TmIndType "nat" [])
            ( TmLambda "H"
              ( TmIndType "eq"
                [ TmIndType "nat" []
                , TmRel "n" 1
                , TmRel "m" 0 ])
              ( TmMatch 2
                ( TmRel "H" 0 )
                  "H0"
                [ "eq"
                , "_"
                , "_"
                , "m0" ]
                ( TmIndType "eq"
                  [ TmIndType "nat" []
                  , TmConstr "S"
                    [ TmRel "n" 4 ]
                  , TmConstr "S"
                    [ TmRel "m0" 1 ]])
                [ Equation
                  [ "eq_refl"
                  , "_"
                  , "_" ]
                  ( TmConstr "eq_refl"
                    [ TmIndType "nat" []
                    , TmConstr "S"
                      [ TmRel "n" 2 ]])]))))
    it "Ind" $
      simplifyIndCmd
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
                    , TmAppl
                      [ TmLambda ".0"
                        ( TmIndType "nat" [])
                        ( TmConstr "S"
                          [ TmRel ".0" 0 ])
                      , TmRel "n" 2 ]]))))
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
                    , TmRel ".1" 0 ])))))]
    it "Theorem" $
      simplifyIndCmd
      ( Theorem "S_Sn"
        ( TmProd "n"
          ( TmIndType "nat" [])
          ( TmAppl
            [ TmLambda "T"
                TmType
              ( TmLambda "x"
                ( TmRel "T" 0 )
                ( TmLambda ".0"
                  ( TmRel "T" 1 )
                  ( TmIndType "eq"
                    [ TmRel "T" 2
                    , TmRel "x" 1
                    , TmRel ".0" 0 ])))
            , TmIndType "nat" []
            , TmRel "n" 0
            , TmAppl
              [ TmLambda ".0"
                ( TmIndType "nat" [])
                ( TmConstr "S"
                  [ TmRel ".0" 0 ])
              , TmRel "n" 0 ]])))
      `shouldBe`
      Theorem "S_Sn"
        ( TmProd "n"
          ( TmIndType "nat" [])
          ( TmIndType "eq"
            [ TmIndType "nat" []
            , TmRel "n" 0
            , TmConstr "S"
              [ TmRel "n" 0 ]]))