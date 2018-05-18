module MiniProver.Core.TerminationSpec (main, spec) where

import           Data.List                   (lookup)
import           Data.Maybe                  (fromJust)
import           MiniProver.Core.Syntax
import           MiniProver.Core.Termination
import           Test.Hspec

main :: IO ()
main = hspec spec

spec :: Spec
spec =
  describe "termination" $ do
    it "plus-yes1" $
      isTerminating
      ( TmFix (-1)
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
              ( TmMatch
                ( TmRel "a" 1)
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
                        , TmRel "b" 1]])])))))
      `shouldBe` Just 1
    it "plus-no1" $
      isTerminating 
      ( TmFix (-1)
        ( TmLambda "plus" 
          ( TmProd "x" 
            ( TmIndType "nat" []) 
            ( TmProd "y" 
              ( TmIndType "nat" []) 
              ( TmIndType "nat" []))) 
          ( TmLambda "x" 
            ( TmIndType "nat" []) 
            ( TmLambda "y" 
              ( TmIndType "nat" []) 
              ( TmMatch 
                ( TmRel "x" 1) ["nat"] 
                  ( TmIndType "nat" []) 
                  [ Equation ["O"] 
                    ( TmAppl 
                      [ TmRel "plus" 2
                      , TmRel "x" 1
                      , TmRel "y" 0])
                  , Equation ["S","n"] 
                    ( TmAppl 
                      [ TmLambda ".0" 
                        ( TmIndType "nat" []) 
                        ( TmConstr "S" 
                          [ TmRel ".0" 0])
                      , TmAppl 
                        [ TmRel "plus" 3
                        , TmRel "n" 0
                        , TmRel "y" 1]])])))))
      `shouldBe` Nothing
    it "plus-no2" $
      isTerminating 
      ( TmFix (-1)
        ( TmLambda "plus"
          ( TmProd "x"
            ( TmIndType "nat" [])
            ( TmProd "y"
              ( TmIndType "nat" [])
              ( TmIndType "nat" [])))
          ( TmLambda "x"
            ( TmIndType "nat" [])
            ( TmLambda "y"
              ( TmIndType "nat" [])
              ( TmMatch
                ( TmRel "x" 1 )
                [ "nat" ]
                ( TmIndType "nat" [])
                [ Equation
                  [ "O" ]
                  ( TmAppl
                    [ TmRel "plus" 2
                    , TmConstr "O" []
                    , TmRel "y" 0 ])
                , Equation
                  [ "S"
                  , "n" ]
                  ( TmAppl
                    [ TmLambda ".0"
                      ( TmIndType "nat" [])
                      ( TmConstr "S"
                        [ TmRel ".0" 0 ])
                    , TmAppl
                      [ TmRel "plus" 3
                      , TmRel "n" 0
                      , TmRel "y" 1 ]])])))))
      `shouldBe` Nothing
    it "plus-yes3" $
      isTerminating 
      ( TmFix (-1)
        ( TmLambda "plus"
          ( TmProd "x"
            ( TmIndType "nat" [])
            ( TmProd "y"
              ( TmIndType "nat" [])
              ( TmIndType "nat" [])))
          ( TmLambda "x"
            ( TmIndType "nat" [])
            ( TmLambda "y"
              ( TmIndType "nat" [])
              ( TmMatch
                ( TmRel "y" 0 )
                [ "nat" ]
                ( TmIndType "nat" [])
                [ Equation
                  [ "O" ]
                  ( TmRel "x" 1 )
                , Equation
                  [ "S"
                  , "n" ]
                  ( TmAppl
                    [ TmLambda ".0"
                      ( TmIndType "nat" [])
                      ( TmConstr "S"
                        [ TmRel ".0" 0 ])
                    , TmAppl
                      [ TmRel "plus" 3
                      , TmRel "x" 2
                      , TmRel "n" 0 ]])])))))
      `shouldBe` Just 2
    it "f-match-no1" $
      isTerminating 
      ( TmFix (-1)
        ( TmLambda "f"
          ( TmProd "x"
            ( TmIndType "nat" [])
            ( TmProd "y"
              ( TmIndType "nat" [])
              ( TmProd "z"
                ( TmIndType "nat" [])
                ( TmIndType "nat" []))))
          ( TmLambda "x"
            ( TmIndType "nat" [])
            ( TmLambda "y"
              ( TmIndType "nat" [])
              ( TmLambda "z"
                ( TmIndType "nat" [])
                ( TmMatch
                  ( TmRel "x" 2 )
                  [ "nat" ]
                  ( TmIndType "nat" [])
                  [ Equation
                    [ "O" ]
                    ( TmAppl
                      [ TmLambda ".0"
                        ( TmIndType "nat" [])
                        ( TmConstr "S"
                          [ TmRel ".0" 0 ])
                      , TmMatch
                        ( TmRel "y" 1 )
                        [ "nat" ]
                        ( TmIndType "nat" [])
                        [ Equation
                          [ "O" ]
                          ( TmRel "x" 2 )
                        , Equation
                          [ "S"
                          , "n" ]
                          ( TmAppl
                            [ TmRel "f" 4
                            , TmRel "x" 3
                            , TmRel "n" 0
                            , TmRel "z" 1 ])]])
                  , Equation
                    [ "S"
                    , "n" ]
                    ( TmAppl
                      [ TmLambda ".0"
                        ( TmIndType "nat" [])
                        ( TmConstr "S"
                          [ TmRel ".0" 0 ])
                      , TmAppl
                        [ TmRel "f" 4
                        , TmRel "n" 0
                        , TmRel "y" 2
                        , TmRel "z" 1 ]])]))))))
      `shouldBe` Nothing
    it "f-match-no2" $
      isTerminating 
      ( TmFix (-1)
        ( TmLambda "f"
          ( TmProd "x"
            ( TmIndType "nat" [])
            ( TmProd "y"
              ( TmIndType "nat" [])
              ( TmProd "z"
                ( TmIndType "nat" [])
                ( TmIndType "nat" []))))
          ( TmLambda "x"
            ( TmIndType "nat" [])
            ( TmLambda "y"
              ( TmIndType "nat" [])
              ( TmLambda "z"
                ( TmIndType "nat" [])
                ( TmMatch
                  ( TmRel "x" 2 )
                  [ "nat" ]
                  ( TmIndType "nat" [])
                  [ Equation
                    [ "O" ]
                    ( TmAppl
                      [ TmLambda ".0"
                        ( TmIndType "nat" [])
                        ( TmConstr "S"
                          [ TmRel ".0" 0 ])
                      , TmMatch
                        ( TmRel "y" 1 )
                        [ "nat" ]
                        ( TmIndType "nat" [])
                        [ Equation
                          [ "O" ]
                          ( TmRel "x" 2 )
                        , Equation
                          [ "S"
                          , "n" ]
                          ( TmAppl
                            [ TmRel "f" 4
                            , TmRel "x" 3
                            , TmRel "n" 0
                            , TmRel "z" 1 ])]])
                  , Equation
                    [ "S"
                    , "n" ]
                    ( TmMatch
                      ( TmRel "z" 1 )
                      [ "nat" ]
                      ( TmIndType "nat" [])
                      [ Equation
                        [ "O" ]
                        ( TmAppl
                          [ TmRel "f" 4
                          , TmConstr "O" []
                          , TmConstr "O" []
                          , TmConstr "O" []])
                      , Equation
                        [ "S"
                        , "n" ]
                        ( TmAppl
                          [ TmRel "f" 5
                          , TmRel "x" 4
                          , TmConstr "O" []
                          , TmRel "n" 0 ])])]))))))
      `shouldBe` Nothing
    it "f-match-yes1" $
      isTerminating 
      ( TmFix (-1)
        ( TmLambda "f"
          ( TmProd "x"
            ( TmIndType "nat" [])
            ( TmProd "y"
              ( TmIndType "nat" [])
              ( TmProd "z"
                ( TmIndType "nat" [])
                ( TmIndType "nat" []))))
          ( TmLambda "x"
            ( TmIndType "nat" [])
            ( TmLambda "y"
              ( TmIndType "nat" [])
              ( TmLambda "z"
                ( TmIndType "nat" [])
                ( TmMatch
                  ( TmRel "x" 2 )
                  [ "nat" ]
                  ( TmIndType "nat" [])
                  [ Equation
                    [ "O" ]
                    ( TmAppl
                      [ TmLambda ".0"
                        ( TmIndType "nat" [])
                        ( TmConstr "S"
                          [ TmRel ".0" 0 ])
                      , TmMatch
                        ( TmRel "y" 1 )
                        [ "nat" ]
                        ( TmIndType "nat" [])
                        [ Equation
                          [ "O" ]
                          ( TmRel "x" 2 )
                        , Equation
                          [ "S"
                          , "n" ]
                          ( TmAppl
                            [ TmRel "f" 4
                            , TmRel "x" 3
                            , TmRel "n" 0
                            , TmRel "z" 1 ])]])
                  , Equation
                    [ "S"
                    , "n" ]
                    ( TmMatch
                      ( TmRel "y" 2 )
                      [ "nat" ]
                      ( TmIndType "nat" [])
                      [ Equation
                        [ "O" ]
                        ( TmConstr "O" [])
                      , Equation
                        [ "S"
                        , "n" ]
                        ( TmAppl
                          [ TmRel "f" 5
                          , TmRel "x" 4
                          , TmRel "n" 0
                          , TmRel "n" 0 ])])]))))))
      `shouldBe` Just 2
    it "f-lambda-no1" $
      isTerminating 
      ( TmFix (-1)
        ( TmLambda "f"
          ( TmProd "x"
            ( TmIndType "nat" [])
            ( TmProd "y"
              ( TmIndType "nat" [])
              ( TmProd "z"
                ( TmIndType "nat" [])
                ( TmProd "w"
                  ( TmIndType "nat" [])
                  ( TmIndType "nat" [])))))
          ( TmLambda "x"
            ( TmIndType "nat" [])
            ( TmLambda "y"
              ( TmIndType "nat" [])
              ( TmLambda "z"
                ( TmIndType "nat" [])
                ( TmLambda "w"
                  ( TmIndType "nat" [])
                  ( TmMatch
                    ( TmRel "x" 3 )
                    [ "nat" ]
                    ( TmIndType "nat" [])
                    [ Equation
                      [ "O" ]
                      ( TmAppl
                        [ TmLambda ".0"
                          ( TmIndType "nat" [])
                          ( TmConstr "S"
                            [ TmRel ".0" 0 ])
                        , TmMatch
                          ( TmRel "y" 2 )
                          [ "nat" ]
                          ( TmIndType "nat" [])
                          [ Equation
                            [ "O" ]
                            ( TmRel "x" 3 )
                          , Equation
                            [ "S"
                            , "n" ]
                            ( TmAppl
                              [ TmRel "f" 5
                              , TmRel "x" 4
                              , TmRel "n" 0
                              , TmRel "z" 2
                              , TmRel "w" 1 ])]])
                    , Equation
                      [ "S"
                      , "n" ]
                      ( TmMatch
                        ( TmRel "y" 3 )
                        [ "nat" ]
                        ( TmIndType "nat" [])
                        [ Equation
                          [ "O" ]
                          ( TmConstr "O" [])
                        , Equation
                          [ "S"
                          , "n" ]
                          ( TmAppl
                            [ TmLambda "c"
                              ( TmIndType "nat" [])
                              ( TmAppl
                                [ TmRel "f" 7
                                , TmRel "x" 6
                                , TmRel "c" 0
                                , TmRel "n" 1
                                , TmRel "w" 3 ])
                            , TmRel "n" 0 ])])])))))))
      `shouldBe` Nothing
    it "f-lambda-yes1" $
      isTerminating 
      ( TmFix (-1)
        ( TmLambda "f"
          ( TmProd "x"
            ( TmIndType "nat" [])
            ( TmProd "y"
              ( TmIndType "nat" [])
              ( TmProd "z"
                ( TmIndType "nat" [])
                ( TmProd "w"
                  ( TmIndType "nat" [])
                  ( TmIndType "nat" [])))))
          ( TmLambda "x"
            ( TmIndType "nat" [])
            ( TmLambda "y"
              ( TmIndType "nat" [])
              ( TmLambda "z"
                ( TmIndType "nat" [])
                ( TmLambda "w"
                  ( TmIndType "nat" [])
                  ( TmMatch
                    ( TmRel "x" 3 )
                    [ "nat" ]
                    ( TmIndType "nat" [])
                    [ Equation
                      [ "O" ]
                      ( TmAppl
                        [ TmLambda ".0"
                          ( TmIndType "nat" [])
                          ( TmConstr "S"
                            [ TmRel ".0" 0 ])
                        , TmMatch
                          ( TmRel "y" 2 )
                          [ "nat" ]
                          ( TmIndType "nat" [])
                          [ Equation
                            [ "O" ]
                            ( TmRel "x" 3 )
                          , Equation
                            [ "S"
                            , "n" ]
                            ( TmAppl
                              [ TmRel "f" 5
                              , TmRel "x" 4
                              , TmRel "n" 0
                              , TmRel "z" 2
                              , TmRel "w" 1 ])]])
                    , Equation
                      [ "S"
                      , "n" ]
                      ( TmMatch
                        ( TmRel "y" 3 )
                        [ "nat" ]
                        ( TmIndType "nat" [])
                        [ Equation
                          [ "O" ]
                          ( TmConstr "O" [])
                        , Equation
                          [ "S"
                          , "n" ]
                          ( TmAppl
                            [ TmLambda "c"
                              ( TmIndType "nat" [])
                              ( TmAppl
                                [ TmRel "f" 7
                                , TmRel "x" 6
                                , TmRel "n" 1
                                , TmRel "c" 0
                                , TmRel "w" 3 ])
                            , TmRel "n" 0 ])])])))))))      
      `shouldBe` Just 2
    it "f-fix-yes1" $
      isTerminating 
      ( TmFix (-1)
        ( TmLambda "f"
          ( TmProd "x"
            ( TmIndType "nat" [])
            ( TmProd "y"
              ( TmIndType "nat" [])
              ( TmProd "z"
                ( TmIndType "nat" [])
                ( TmIndType "nat" []))))
          ( TmLambda "x"
            ( TmIndType "nat" [])
            ( TmLambda "y"
              ( TmIndType "nat" [])
              ( TmLambda "z"
                ( TmIndType "nat" [])
                ( TmMatch
                  ( TmRel "x" 2 )
                  [ "nat" ]
                  ( TmIndType "nat" [])
                  [ Equation
                    [ "O" ]
                    ( TmLambda ".0"
                      ( TmIndType "nat" [])
                      ( TmConstr "S"
                        [ TmRel ".0" 0 ]))
                  , Equation
                    [ "S"
                    , "n" ]
                    ( TmAppl
                      [ TmFix (-1)
                        ( TmLambda "plus"
                          ( TmProd "x"
                            ( TmIndType "nat" [])
                            ( TmIndType "nat" []))
                          ( TmLambda "x"
                            ( TmIndType "nat" [])
                            ( TmMatch
                              ( TmRel "x" 0 )
                              [ "nat" ]
                              ( TmIndType "nat" [])
                              [ Equation
                                [ "O" ]
                                ( TmRel "y" 4 )
                              , Equation
                                [ "S"
                                , "m" ]
                                ( TmAppl
                                  [ TmRel "f" 7
                                  , TmRel "n" 3
                                  , TmRel "m" 0
                                  , TmRel "z" 4 ])])))
                      , TmRel "y" 2 ])]))))))
      `shouldBe` Just 1
    it "f-fix-no1" $
      isTerminating 
      ( TmFix (-1)
        ( TmLambda "f"
          ( TmProd "x"
            ( TmIndType "nat" [])
            ( TmProd "y"
              ( TmIndType "nat" [])
              ( TmProd "z"
                ( TmIndType "nat" [])
                ( TmIndType "nat" []))))
          ( TmLambda "x"
            ( TmIndType "nat" [])
            ( TmLambda "y"
              ( TmIndType "nat" [])
              ( TmLambda "z"
                ( TmIndType "nat" [])
                ( TmMatch
                  ( TmRel "x" 2 )
                  [ "nat" ]
                  ( TmIndType "nat" [])
                  [ Equation
                    [ "O" ]
                    ( TmLambda ".0"
                      ( TmIndType "nat" [])
                      ( TmConstr "S"
                        [ TmRel ".0" 0 ]))
                  , Equation
                    [ "S"
                    , "n" ]
                    ( TmAppl
                      [ TmFix (-1)
                        ( TmLambda "plus"
                          ( TmProd "x"
                            ( TmIndType "nat" [])
                            ( TmIndType "nat" []))
                          ( TmLambda "x"
                            ( TmIndType "nat" [])
                            ( TmMatch
                              ( TmRel "x" 0 )
                              [ "nat" ]
                              ( TmIndType "nat" [])
                              [ Equation
                                [ "O" ]
                                ( TmRel "y" 4 )
                              , Equation
                                [ "S"
                                , "m" ]
                                ( TmAppl
                                  [ TmRel "f" 7
                                  , TmRel "m" 0
                                  , TmRel "n" 3
                                  , TmRel "z" 4 ])])))
                      , TmRel "y" 2 ])]))))))
      `shouldBe` Nothing
    it "f-let-no1" $
      isTerminating 
      ( TmFix (-1)
        ( TmLambda "f"
          ( TmProd "x"
            ( TmIndType "nat" [])
            ( TmProd "y"
              ( TmIndType "nat" [])
              ( TmProd "z"
                ( TmIndType "nat" [])
                ( TmIndType "nat" []))))
          ( TmLambda "x"
            ( TmIndType "nat" [])
            ( TmLambda "y"
              ( TmIndType "nat" [])
              ( TmLambda "z"
                ( TmIndType "nat" [])
                ( TmMatch
                  ( TmRel "x" 2 )
                  [ "nat" ]
                  ( TmIndType "nat" [])
                  [ Equation
                    [ "O" ]
                    ( TmLambda ".0"
                      ( TmIndType "nat" [])
                      ( TmConstr "S"
                        [ TmRel ".0" 0 ]))
                  , Equation
                    [ "S"
                    , "n" ]
                    ( TmLetIn "g"
                      ( TmProd "_"
                        ( TmIndType "nat" [])
                        ( TmIndType "nat" []))
                      ( TmFix (-1)
                        ( TmLambda "plus"
                          ( TmProd "x"
                            ( TmIndType "nat" [])
                            ( TmIndType "nat" []))
                          ( TmLambda "x"
                            ( TmIndType "nat" [])
                            ( TmMatch
                              ( TmRel "x" 0 )
                              [ "nat" ]
                              ( TmIndType "nat" [])
                              [ Equation
                                [ "O" ]
                                ( TmRel "y" 4 )
                              , Equation
                                [ "S"
                                , "m" ]
                                ( TmAppl
                                  [ TmRel "plus" 2
                                  , TmAppl
                                    [ TmRel "f" 7
                                    , TmAppl
                                      [ TmRel "plus" 2
                                      , TmRel "m" 0 ]
                                    , TmRel "n" 3
                                    , TmRel "y" 5 ]])]))))
                      ( TmAppl
                        [ TmRel "g" 0
                        , TmRel "y" 3 ]))]))))))
      `shouldBe` Nothing
    it "f-let-yes1" $
      isTerminating 
      ( TmFix (-1)
        ( TmLambda "f"
          ( TmProd "x"
            ( TmIndType "nat" [])
            ( TmProd "y"
              ( TmIndType "nat" [])
              ( TmProd "z"
                ( TmIndType "nat" [])
                ( TmIndType "nat" []))))
          ( TmLambda "x"
            ( TmIndType "nat" [])
            ( TmLambda "y"
              ( TmIndType "nat" [])
              ( TmLambda "z"
                ( TmIndType "nat" [])
                ( TmMatch
                  ( TmRel "x" 2 )
                  [ "nat" ]
                  ( TmIndType "nat" [])
                  [ Equation
                    [ "O" ]
                    ( TmLambda ".0"
                      ( TmIndType "nat" [])
                      ( TmConstr "S"
                        [ TmRel ".0" 0 ]))
                  , Equation
                    [ "S"
                    , "n" ]
                    ( TmLetIn "g"
                      ( TmProd "_"
                        ( TmIndType "nat" [])
                        ( TmIndType "nat" []))
                      ( TmFix (-1)
                        ( TmLambda "plus"
                          ( TmProd "x"
                            ( TmIndType "nat" [])
                            ( TmIndType "nat" []))
                          ( TmLambda "x"
                            ( TmIndType "nat" [])
                            ( TmMatch
                              ( TmRel "x" 0 )
                              [ "nat" ]
                              ( TmIndType "nat" [])
                              [ Equation
                                [ "O" ]
                                ( TmRel "y" 4 )
                              , Equation
                                [ "S"
                                , "m" ]
                                ( TmAppl
                                  [ TmRel "plus" 2
                                  , TmAppl
                                    [ TmRel "f" 7
                                    , TmRel "n" 3
                                    , TmAppl
                                      [ TmRel "plus" 2
                                      , TmRel "m" 0 ]
                                    , TmRel "x" 1 ]])]))))
                      ( TmAppl
                        [ TmRel "g" 0
                        , TmRel "y" 3 ]))]))))))
      `shouldBe` Just 1
    it "f-let-yes2" $
      isTerminating 
      ( TmFix (-1)
        ( TmLambda "f"
          ( TmProd "x"
            ( TmIndType "nat" [])
            ( TmProd "y"
              ( TmIndType "nat" [])
              ( TmProd "z"
                ( TmIndType "nat" [])
                ( TmIndType "nat" []))))
          ( TmLambda "x"
            ( TmIndType "nat" [])
            ( TmLambda "y"
              ( TmIndType "nat" [])
              ( TmLambda "z"
                ( TmIndType "nat" [])
                ( TmMatch
                  ( TmRel "x" 2 )
                  [ "nat" ]
                  ( TmIndType "nat" [])
                  [ Equation
                    [ "O" ]
                    ( TmLetIn "g"
                      ( TmIndType "nat" [])
                      ( TmRel "y" 1 )
                      ( TmRel "g" 0 ))
                  , Equation
                    [ "S"
                    , "n" ]
                    ( TmLetIn "g"
                      ( TmProd "_"
                        ( TmIndType "nat" [])
                        ( TmIndType "nat" []))
                      ( TmFix (-1)
                        ( TmLambda "plus"
                          ( TmProd "x"
                            ( TmIndType "nat" [])
                            ( TmIndType "nat" []))
                          ( TmLambda "x"
                            ( TmIndType "nat" [])
                            ( TmMatch
                              ( TmRel "x" 0 )
                              [ "nat" ]
                              ( TmIndType "nat" [])
                              [ Equation
                                [ "O" ]
                                ( TmRel "y" 4 )
                              , Equation
                                [ "S"
                                , "m" ]
                                ( TmAppl
                                  [ TmRel "plus" 2
                                  , TmAppl
                                    [ TmRel "f" 7
                                    , TmRel "n" 3
                                    , TmAppl
                                      [ TmRel "plus" 2
                                      , TmRel "m" 0 ]
                                    , TmRel "x" 1 ]])]))))
                      ( TmAppl
                        [ TmRel "g" 0
                        , TmAppl
                          [ TmRel "f" 5
                          , TmRel "n" 1
                          , TmRel "n" 1
                          , TmRel "n" 1 ]]))]))))))
      `shouldBe` Just 1
    it "deep-match-yes1" $
      isTerminating 
      ( TmFix (-1)
        ( TmLambda "f"
          ( TmProd "x"
            ( TmIndType "nat" [])
            ( TmProd "y"
              ( TmIndType "nat" [])
              ( TmProd "z"
                ( TmIndType "nat" [])
                ( TmIndType "nat" []))))
          ( TmLambda "x"
            ( TmIndType "nat" [])
            ( TmLambda "y"
              ( TmIndType "nat" [])
              ( TmLambda "z"
                ( TmIndType "nat" [])
                ( TmMatch
                  ( TmRel "x" 2 )
                  [ "nat" ]
                  ( TmIndType "nat" [])
                  [ Equation
                    [ "O" ]
                    ( TmConstr "O" [])
                  , Equation
                    [ "S"
                    , "nx" ]
                    ( TmMatch
                      ( TmRel "y" 2 )
                      [ "nat" ]
                      ( TmIndType "nat" [])
                      [ Equation
                        [ "O" ]
                        ( TmRel "y" 2 )
                      , Equation
                        [ "S"
                        , "ny" ]
                        ( TmAppl
                          [ TmRel "f" 5
                          , TmMatch
                            ( TmRel "z" 2 )
                            [ "nat" ]
                            ( TmIndType "nat" [])
                            [ Equation
                              [ "O" ]
                              ( TmConstr "O" [])
                            , Equation
                              [ "S"
                              , "nz" ]
                              ( TmAppl
                                [ TmRel "f" 6
                                , TmRel "nx" 2
                                , TmRel "ny" 1
                                , TmRel "nz" 0 ])]
                          , TmRel "ny" 0
                          , TmRel "z" 2 ])])]))))))
      `shouldBe` Just 2
