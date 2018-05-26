module MiniProver.Core.TerminationSpec (main, spec) where

import           Data.List                   (lookup)
import           Data.Maybe                  (fromJust)
import           MiniProver.Core.Syntax
--import           MiniProver.Core.Termination
import           Test.Hspec

main :: IO ()
main = hspec spec
isTerminating :: Term -> Maybe Int
isTerminating = undefined
computeDecParam :: Term -> Either Term Term
computeDecParam = undefined
computeDecParamCmd :: Command -> Either Term Command
computeDecParamCmd = undefined

spec :: Spec
spec = do
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
              ( TmMatch 0
                ( TmRel "a" 1)
                "a0"
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
              ( TmMatch 0
                ( TmRel "x" 1) "x0" ["nat"]
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
              ( TmMatch 0
                ( TmRel "x" 1 )
                "x0"
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
              ( TmMatch 0
                ( TmRel "y" 0 )
                "y0"
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
                ( TmMatch 0
                  ( TmRel "x" 2 )
                  "x0"
                  [ "nat" ]
                  ( TmIndType "nat" [])
                  [ Equation
                    [ "O" ]
                    ( TmAppl
                      [ TmLambda ".0"
                        ( TmIndType "nat" [])
                        ( TmConstr "S"
                          [ TmRel ".0" 0 ])
                      , TmMatch 0
                        ( TmRel "y" 1 )
                        "y0"
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
                ( TmMatch 0
                  ( TmRel "x" 2 )
                  "x0"
                  [ "nat" ]
                  ( TmIndType "nat" [])
                  [ Equation
                    [ "O" ]
                    ( TmAppl
                      [ TmLambda ".0"
                        ( TmIndType "nat" [])
                        ( TmConstr "S"
                          [ TmRel ".0" 0 ])
                      , TmMatch 0
                        ( TmRel "y" 1 )
                        "y0"
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
                    ( TmMatch 0
                      ( TmRel "z" 1 )
                      "z0"
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
                ( TmMatch 0
                  ( TmRel "x" 2 )
                  "x0"
                  [ "nat" ]
                  ( TmIndType "nat" [])
                  [ Equation
                    [ "O" ]
                    ( TmAppl
                      [ TmLambda ".0"
                        ( TmIndType "nat" [])
                        ( TmConstr "S"
                          [ TmRel ".0" 0 ])
                      , TmMatch 0
                        ( TmRel "y" 1 )
                        "y0"
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
                    ( TmMatch 0
                      ( TmRel "y" 2 )
                      "y0"
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
                  ( TmMatch 0
                    ( TmRel "x" 3 )
                    "x0"
                    [ "nat" ]
                    ( TmIndType "nat" [])
                    [ Equation
                      [ "O" ]
                      ( TmAppl
                        [ TmLambda ".0"
                          ( TmIndType "nat" [])
                          ( TmConstr "S"
                            [ TmRel ".0" 0 ])
                        , TmMatch 0
                          ( TmRel "y" 2 )
                          "y0"
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
                      ( TmMatch 0
                        ( TmRel "y" 3 )
                        "y0"
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
                  ( TmMatch 0
                    ( TmRel "x" 3 )
                    "x0"
                    [ "nat" ]
                    ( TmIndType "nat" [])
                    [ Equation
                      [ "O" ]
                      ( TmAppl
                        [ TmLambda ".0"
                          ( TmIndType "nat" [])
                          ( TmConstr "S"
                            [ TmRel ".0" 0 ])
                        , TmMatch 0
                          ( TmRel "y" 2 )
                          "y0"
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
                      ( TmMatch 0
                        ( TmRel "y" 3 )
                        "y0"
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
                ( TmMatch 0
                  ( TmRel "x" 2 )
                  "x0"
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
                            ( TmMatch 0
                              ( TmRel "x" 0 )
                              "x0"
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
                ( TmMatch 0
                  ( TmRel "x" 2 )
                  "x0"
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
                            ( TmMatch 0
                              ( TmRel "x" 0 )
                              "x0"
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
                ( TmMatch 0
                  ( TmRel "x" 2 )
                  "x0"
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
                            ( TmMatch 0
                              ( TmRel "x" 0 )
                              "x0"
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
                ( TmMatch 0
                  ( TmRel "x" 2 )
                  "x0"
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
                            ( TmMatch 0
                              ( TmRel "x" 0 )
                              "x0"
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
                ( TmMatch 0
                  ( TmRel "x" 2 )
                  "x0"
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
                            ( TmMatch 0
                              ( TmRel "x" 0 )
                              "x0"
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
                ( TmMatch 0
                  ( TmRel "x" 2 )
                  "x0"
                  [ "nat" ]
                  ( TmIndType "nat" [])
                  [ Equation
                    [ "O" ]
                    ( TmConstr "O" [])
                  , Equation
                    [ "S"
                    , "nx" ]
                    ( TmMatch 0
                      ( TmRel "y" 2 )
                      "y0"
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
                          , TmMatch 0
                            ( TmRel "z" 2 )
                            "z0"
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
    it "dependent pattern matching" $
      isTerminating
      ( TmLambda "app"
        ( TmProd "n1"
          ( TmIndType "nat" [])
          ( TmProd "ls1"
            ( TmAppl
              [ TmLambda "T"
                  TmType
                ( TmLambda ".0"
                  ( TmIndType "nat" [])
                  ( TmIndType "ilist"
                    [ TmRel "T" 1
                    , TmRel ".0" 0 ]))
              , TmIndType "nat" []
              , TmRel "n1" 0 ])
            ( TmProd "n2"
              ( TmIndType "nat" [])
              ( TmProd "ls2"
                ( TmAppl
                  [ TmLambda "T"
                      TmType
                    ( TmLambda ".0"
                      ( TmIndType "nat" [])
                      ( TmIndType "ilist"
                        [ TmRel "T" 1
                        , TmRel ".0" 0 ]))
                  , TmIndType "nat" []
                  , TmRel "n2" 0 ])
                ( TmAppl
                  [ TmLambda "T"
                      TmType
                    ( TmLambda ".0"
                      ( TmIndType "nat" [])
                      ( TmIndType "ilist"
                        [ TmRel "T" 1
                        , TmRel ".0" 0 ]))
                  , TmIndType "nat" []
                  , TmAppl
                    [ TmRel "plus" 5
                    , TmRel "n1" 3
                    , TmRel "n2" 1 ]])))))
        ( TmLambda "n1"
          ( TmIndType "nat" [])
          ( TmLambda "ls1"
            ( TmAppl
              [ TmLambda "T"
                  TmType
                ( TmLambda ".0"
                  ( TmIndType "nat" [])
                  ( TmIndType "ilist"
                    [ TmRel "T" 1
                    , TmRel ".0" 0 ]))
              , TmIndType "nat" []
              , TmRel "n1" 0 ])
            ( TmLambda "n2"
              ( TmIndType "nat" [])
              ( TmLambda "ls2"
                ( TmAppl
                  [ TmLambda "T"
                      TmType
                    ( TmLambda ".0"
                      ( TmIndType "nat" [])
                      ( TmIndType "ilist"
                        [ TmRel "T" 1
                        , TmRel ".0" 0 ]))
                  , TmIndType "nat" []
                  , TmRel "n2" 0 ])
                ( TmMatch 1
                  ( TmRel "ls1" 2 )
                    "lss0"
                  [ "ilist"
                  , "_"
                  , "n1" ]
                  ( TmAppl
                    [ TmLambda "T"
                        TmType
                      ( TmLambda ".0"
                        ( TmIndType "nat" [])
                        ( TmIndType "ilist"
                          [ TmRel "T" 1
                          , TmRel ".0" 0 ]))
                    , TmIndType "nat" []
                    , TmAppl
                      [ TmRel "plus" 8
                      , TmRel "n1" 1
                      , TmRel "n2" 3 ]])
                  [ Equation
                    [ "inil"
                    , "_" ]
                    ( TmRel "ls2" 0 )
                  , Equation
                    [ "icons"
                    , "_"
                    , "n"
                    , "hd"
                    , "tl" ]
                    ( TmAppl
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
                      , TmIndType "nat" []
                      , TmAppl
                        [ TmRel "plus" 9
                        , TmRel "n" 2
                        , TmRel "n2" 4 ]
                      , TmRel "hd" 1
                      , TmAppl
                        [ TmRel "app" 7
                        , TmRel "n" 2
                        , TmRel "tl" 0
                        , TmRel "n2" 4
                        , TmRel "ls2" 3 ]])]))))))
      `shouldBe` Just 2
  describe "computeDecParam" $ do
    it "TmRel" $
      computeDecParam (TmRel "x" 0) `shouldBe` Right (TmRel "x" 0)
    it "TmAppl" $
      computeDecParam
      ( TmAppl
        [ TmFix (-1)
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
                ( TmMatch 0
                  ( TmRel "x" 1 )
                  "x0"
                  [ "nat" ]
                  ( TmIndType "nat" [])
                  [ Equation
                    [ "O" ]
                    ( TmRel "y" 0 )
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
                        , TmRel "y" 1 ]])]))))
        , TmAppl
          [ TmLambda ".0"
            ( TmIndType "nat" [])
            ( TmConstr "S"
              [ TmRel ".0" 0 ])
          , TmAppl
            [ TmLambda ".0"
              ( TmIndType "nat" [])
              ( TmConstr "S"
                [ TmRel ".0" 0 ])
            , TmConstr "O" []]]
        , TmConstr "O" []])
      `shouldBe`
      Right
      ( TmAppl
        [ TmFix 1
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
                ( TmMatch 0
                  ( TmRel "x" 1 )
                  "x0"
                  [ "nat" ]
                  ( TmIndType "nat" [])
                  [ Equation
                    [ "O" ]
                    ( TmRel "y" 0 )
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
                        , TmRel "y" 1 ]])]))))
        , TmAppl
          [ TmLambda ".0"
            ( TmIndType "nat" [])
            ( TmConstr "S"
              [ TmRel ".0" 0 ])
          , TmAppl
            [ TmLambda ".0"
              ( TmIndType "nat" [])
              ( TmConstr "S"
                [ TmRel ".0" 0 ])
            , TmConstr "O" []]]
        , TmConstr "O" []])
    it "TmLambda/TmMatch" $
      computeDecParam
      ( TmLambda "x"
          ( TmIndType "nat" [])
          ( TmLambda "y"
            ( TmIndType "nat" [])
            ( TmLambda "z"
              ( TmIndType "nat" [])
              ( TmMatch 0
                ( TmRel "x" 2 )
                "x0"
                [ "nat" ]
                ( TmIndType "nat" [])
                [ Equation
                  [ "O" ]
                  ( TmMatch 0
                    ( TmRel "y" 1 )
                    "y0"
                    [ "nat" ]
                    ( TmIndType "nat" [])
                    [ Equation
                      [ "O" ]
                      ( TmRel "z" 0 )
                    , Equation
                      [ "S"
                      , "n" ]
                      ( TmAppl
                        [ TmFix (-1)
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
                    [ TmFix (-1)
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
                        "y0"
                        [ "nat" ]
                        ( TmIndType "nat" [])
                        [ Equation
                          [ "O" ]
                          ( TmRel "z" 1 )
                        , Equation
                          [ "S"
                          , "n" ]
                          ( TmAppl
                            [ TmFix (-1)
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
                              [ TmRel "z" 2 ]])]]])]))))
      `shouldBe`
      Right
      ( TmLambda "x"
          ( TmIndType "nat" [])
          ( TmLambda "y"
            ( TmIndType "nat" [])
            ( TmLambda "z"
              ( TmIndType "nat" [])
              ( TmMatch 0
                ( TmRel "x" 2 )
                "x0"
                [ "nat" ]
                ( TmIndType "nat" [])
                [ Equation
                  [ "O" ]
                  ( TmMatch 0
                    ( TmRel "y" 1 )
                    "y0"
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
                        "y0"
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
                              [ TmRel "z" 2 ]])]]])]))))
    it "TmProd" $
      computeDecParam
      ( TmProd "x"
        ( TmIndType "nat" [])
        ( TmAppl
          [ TmLambda "a"
              TmType
            ( TmLambda ".0"
              ( TmRel "a" 0 )
              ( TmLambda ".1"
                ( TmRel "a" 1 )
                ( TmIndType "eq"
                  [ TmRel "a" 2
                  , TmRel ".0" 1
                  , TmRel ".1" 0 ])))
          , TmIndType "nat" []
          , TmAppl
            [ TmFix (-1)
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
                    ( TmMatch 0
                      ( TmRel "y" 0 )
                      "y0"
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
                            , TmRel "n" 0 ]])]))))
            , TmRel "x" 0
            , TmConstr "O" []]
          , TmRel "x" 0 ]))
      `shouldBe`
      Right
      ( TmProd "x"
        ( TmIndType "nat" [])
        ( TmAppl
          [ TmLambda "a"
              TmType
            ( TmLambda ".0"
              ( TmRel "a" 0 )
              ( TmLambda ".1"
                ( TmRel "a" 1 )
                ( TmIndType "eq"
                  [ TmRel "a" 2
                  , TmRel ".0" 1
                  , TmRel ".1" 0 ])))
          , TmIndType "nat" []
          , TmAppl
            [ TmFix 2
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
                    ( TmMatch 0
                      ( TmRel "y" 0 )
                      "y0"
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
                            , TmRel "n" 0 ]])]))))
            , TmRel "x" 0
            , TmConstr "O" []]
          , TmRel "x" 0 ]))
    it "TmLetIn" $
      computeDecParam
      ( TmLetIn "plus1"
        ( TmProd "_"
          ( TmIndType "nat" [])
          ( TmProd "_"
            ( TmIndType "nat" [])
            ( TmIndType "nat" [])))
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
                ( TmMatch 0
                  ( TmRel "y" 0 )
                  "y0"
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
        ( TmAppl
          [ TmRel "plus1" 0
          , TmAppl
            [ TmFix (-1)
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
                    ( TmMatch 0
                      ( TmRel "x" 1 )
                      "x0"
                      [ "nat" ]
                      ( TmIndType "nat" [])
                      [ Equation
                        [ "O" ]
                        ( TmRel "y" 0 )
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
                            , TmRel "y" 1 ]])]))))
            , TmConstr "O" []
            , TmConstr "O" []]
          , TmConstr "O" []]))
      `shouldBe`
      Right
      ( TmLetIn "plus1"
        ( TmProd "_"
          ( TmIndType "nat" [])
          ( TmProd "_"
            ( TmIndType "nat" [])
            ( TmIndType "nat" [])))
        ( TmFix 2
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
                ( TmMatch 0
                  ( TmRel "y" 0 )
                  "y0"
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
        ( TmAppl
          [ TmRel "plus1" 0
          , TmAppl
            [ TmFix 1
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
                    ( TmMatch 0
                      ( TmRel "x" 1 )
                      "x0"
                      [ "nat" ]
                      ( TmIndType "nat" [])
                      [ Equation
                        [ "O" ]
                        ( TmRel "y" 0 )
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
                            , TmRel "y" 1 ]])]))))
            , TmConstr "O" []
            , TmConstr "O" []]
          , TmConstr "O" []]))
    it "TmIndType/TmConstr" $
      computeDecParam
      ( TmAppl
        [ TmLambda "a"
            TmType
          ( TmLambda ".0"
            ( TmRel "a" 0 )
            ( TmLambda ".1"
              ( TmRel "a" 1 )
              ( TmIndType "eq"
                [ TmRel "a" 2
                , TmRel ".0" 1
                , TmRel ".1" 0 ])))
        , TmIndType "nat" []
        , TmAppl
          [ TmFix (-1)
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
                  ( TmMatch 0
                    ( TmRel "y" 0 )
                    "y0"
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
                          , TmRel "n" 0 ]])]))))
          , TmAppl
            [ TmLambda ".0"
              ( TmIndType "nat" [])
              ( TmConstr "S"
                [ TmRel ".0" 0 ])
            , TmConstr "O" []]
          , TmAppl
            [ TmLambda ".0"
              ( TmIndType "nat" [])
              ( TmConstr "S"
                [ TmRel ".0" 0 ])
            , TmConstr "O" []]]
        , TmAppl
          [ TmLambda ".0"
            ( TmIndType "nat" [])
            ( TmConstr "S"
              [ TmRel ".0" 0 ])
          , TmAppl
            [ TmFix (-1)
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
                    ( TmMatch 0
                      ( TmRel "y" 0 )
                      "y0"
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
                            , TmRel "n" 0 ]])]))))
            , TmAppl
              [ TmLambda ".0"
                ( TmIndType "nat" [])
                ( TmConstr "S"
                  [ TmRel ".0" 0 ])
              , TmConstr "O" []]
            , TmConstr "O" []]]])
      `shouldBe`
      Right
      ( TmAppl
        [ TmLambda "a"
            TmType
          ( TmLambda ".0"
            ( TmRel "a" 0 )
            ( TmLambda ".1"
              ( TmRel "a" 1 )
              ( TmIndType "eq"
                [ TmRel "a" 2
                , TmRel ".0" 1
                , TmRel ".1" 0 ])))
        , TmIndType "nat" []
        , TmAppl
          [ TmFix 2
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
                  ( TmMatch 0
                    ( TmRel "y" 0 )
                    "y0"
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
                          , TmRel "n" 0 ]])]))))
          , TmAppl
            [ TmLambda ".0"
              ( TmIndType "nat" [])
              ( TmConstr "S"
                [ TmRel ".0" 0 ])
            , TmConstr "O" []]
          , TmAppl
            [ TmLambda ".0"
              ( TmIndType "nat" [])
              ( TmConstr "S"
                [ TmRel ".0" 0 ])
            , TmConstr "O" []]]
        , TmAppl
          [ TmLambda ".0"
            ( TmIndType "nat" [])
            ( TmConstr "S"
              [ TmRel ".0" 0 ])
          , TmAppl
            [ TmFix 2
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
                    ( TmMatch 0
                      ( TmRel "y" 0 )
                      "y0"
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
                            , TmRel "n" 0 ]])]))))
            , TmAppl
              [ TmLambda ".0"
                ( TmIndType "nat" [])
                ( TmConstr "S"
                  [ TmRel ".0" 0 ])
              , TmConstr "O" []]
            , TmConstr "O" []]]])
    it "TmAppl-fail" $
      computeDecParam
      ( TmAppl
        [ TmFix (-1)
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
                ( TmMatch  0
                  ( TmRel "x" 1) "x0" ["nat"] 
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
                          , TmRel "y" 1]])]))))
        , TmAppl
          [ TmLambda ".0"
            ( TmIndType "nat" [])
            ( TmConstr "S"
              [ TmRel ".0" 0 ])
          , TmAppl
            [ TmLambda ".0"
              ( TmIndType "nat" [])
              ( TmConstr "S"
                [ TmRel ".0" 0 ])
            , TmConstr "O" []]]
        , TmConstr "O" []])
      `shouldBe`
      Left
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
                ( TmMatch  0
                  ( TmRel "x" 1) "x0" ["nat"] 
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
    it "TmLambda/TmMatch-fail" $
      computeDecParam
      ( TmLambda "x"
          ( TmIndType "nat" [])
          ( TmLambda "y"
            ( TmIndType "nat" [])
            ( TmLambda "z"
              ( TmIndType "nat" [])
              ( TmMatch 0
                ( TmRel "x" 2 )
                "x0"
                [ "nat" ]
                ( TmIndType "nat" [])
                [ Equation
                  [ "O" ]
                  ( TmMatch 0
                    ( TmRel "y" 1 )
                    "y0"
                    [ "nat" ]
                    ( TmIndType "nat" [])
                    [ Equation
                      [ "O" ]
                      ( TmRel "z" 0 )
                    , Equation
                      [ "S"
                      , "n" ]
                      ( TmAppl
                        [ TmFix (-1)
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
                    [ TmFix (-1)
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
                        "y0"
                        [ "nat" ]
                        ( TmIndType "nat" [])
                        [ Equation
                          [ "O" ]
                          ( TmRel "z" 1 )
                        , Equation
                          [ "S"
                          , "n" ]
                          ( TmAppl
                            [ TmFix (-1)
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
                                    ( TmMatch 0
                                      ( TmRel "x" 1) "x0" ["nat"] 
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
                                              , TmRel "y" 1]])]))))
                            , TmRel "n" 0
                            , TmConstr "S"
                              [ TmRel "z" 2 ]])]]])]))))
      `shouldBe`
      Left
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
              ( TmMatch 0
                ( TmRel "x" 1) "x0" ["nat"] 
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
    it "TmProd-fail" $
      computeDecParam
      ( TmProd "x"
        ( TmIndType "nat" [])
        ( TmAppl
          [ TmLambda "a"
              TmType
            ( TmLambda ".0"
              ( TmRel "a" 0 )
              ( TmLambda ".1"
                ( TmRel "a" 1 )
                ( TmIndType "eq"
                  [ TmRel "a" 2
                  , TmRel ".0" 1
                  , TmRel ".1" 0 ])))
          , TmIndType "nat" []
          , TmAppl
            [ TmFix (-1)
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
                    ( TmMatch 0
                      ( TmRel "x" 1) "x0" ["nat"] 
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
                              , TmRel "y" 1]])]))))
            , TmRel "x" 0
            , TmConstr "O" []]
          , TmRel "x" 0 ]))
      `shouldBe`
      Left
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
              ( TmMatch 0
                ( TmRel "x" 1) "x0" ["nat"] 
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
    it "TmLetIn" $
      computeDecParam
      ( TmLetIn "plus1"
        ( TmProd "_"
          ( TmIndType "nat" [])
          ( TmProd "_"
            ( TmIndType "nat" [])
            ( TmIndType "nat" [])))
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
                ( TmMatch 0
                  ( TmRel "y" 0 )
                  "y0"
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
        ( TmAppl
          [ TmRel "plus1" 0
          , TmAppl
            [ TmFix (-1)
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
                    ( TmMatch 0
                      ( TmRel "x" 1) "x0" ["nat"] 
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
                              , TmRel "y" 1]])]))))
            , TmConstr "O" []
            , TmConstr "O" []]
          , TmConstr "O" []]))
      `shouldBe`
      Left
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
              ( TmMatch 0
                ( TmRel "x" 1) "x0" ["nat"] 
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
    it "TmIndType/TmConstr" $
      computeDecParam
      ( TmAppl
        [ TmLambda "a"
            TmType
          ( TmLambda ".0"
            ( TmRel "a" 0 )
            ( TmLambda ".1"
              ( TmRel "a" 1 )
              ( TmIndType "eq"
                [ TmRel "a" 2
                , TmRel ".0" 1
                , TmRel ".1" 0 ])))
        , TmIndType "nat" []
        , TmAppl
          [ TmFix (-1)
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
                  ( TmMatch 0
                    ( TmRel "y" 0 )
                    "y0"
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
                          , TmRel "n" 0 ]])]))))
          , TmAppl
            [ TmLambda ".0"
              ( TmIndType "nat" [])
              ( TmConstr "S"
                [ TmRel ".0" 0 ])
            , TmConstr "O" []]
          , TmAppl
            [ TmLambda ".0"
              ( TmIndType "nat" [])
              ( TmConstr "S"
                [ TmRel ".0" 0 ])
            , TmConstr "O" []]]
        , TmAppl
          [ TmLambda ".0"
            ( TmIndType "nat" [])
            ( TmConstr "S"
              [ TmRel ".0" 0 ])
          , TmAppl
            [ TmFix (-1)
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
                    ( TmMatch 0
                      ( TmRel "x" 1) "x0" ["nat"] 
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
                              , TmRel "y" 1]])]))))
            , TmAppl
              [ TmLambda ".0"
                ( TmIndType "nat" [])
                ( TmConstr "S"
                  [ TmRel ".0" 0 ])
              , TmConstr "O" []]
            , TmConstr "O" []]]])
      `shouldBe`
      Left
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
              ( TmMatch 0
                ( TmRel "x" 1) "x0" ["nat"] 
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
  describe "computeDecParamCmd" $ do
    it "Ax" $
      computeDecParamCmd
      ( Ax "pluscomm"
        ( TmIndType "eq"
          [ TmIndType "nat" []
          , TmAppl
            [ TmFix (-1)
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
                    ( TmMatch 0
                      ( TmRel "x" 1 )
                      "x0"
                      [ "nat" ]
                      ( TmIndType "nat" [])
                      [ Equation
                        [ "O" ]
                        ( TmRel "y" 0 )
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
                            , TmRel "y" 1 ]])]))))
            , TmAppl
              [ TmLambda ".0"
                ( TmIndType "nat" [])
                ( TmConstr "S"
                  [ TmRel ".0" 0 ])
              , TmAppl
                [ TmLambda ".0"
                  ( TmIndType "nat" [])
                  ( TmConstr "S"
                    [ TmRel ".0" 0 ])
                , TmConstr "O" []]]
            , TmConstr "O" []]
            , TmConstr "S"
              [ TmConstr "S"
                [ TmConstr "O" [] ]]]))
      `shouldBe`
      Right
      ( Ax "pluscomm"
        ( TmIndType "eq"
          [ TmIndType "nat" []
          , TmAppl
            [ TmFix 1
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
                    ( TmMatch 0
                      ( TmRel "x" 1 )
                      "x0"
                      [ "nat" ]
                      ( TmIndType "nat" [])
                      [ Equation
                        [ "O" ]
                        ( TmRel "y" 0 )
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
                            , TmRel "y" 1 ]])]))))
            , TmAppl
              [ TmLambda ".0"
                ( TmIndType "nat" [])
                ( TmConstr "S"
                  [ TmRel ".0" 0 ])
              , TmAppl
                [ TmLambda ".0"
                  ( TmIndType "nat" [])
                  ( TmConstr "S"
                    [ TmRel ".0" 0 ])
                , TmConstr "O" []]]
            , TmConstr "O" []]
            , TmConstr "S"
              [ TmConstr "S"
                [ TmConstr "O" [] ]]]))
    it "Def" $
      computeDecParamCmd
      ( Def "plus"
        ( TmProd "x"
          ( TmIndType "nat" [] )
          ( TmProd "y"
            ( TmIndType "nat" [] )
            ( TmIndType "nat" [] )))
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
                ( TmMatch 0
                  ( TmRel "x" 1 )
                  "x0"
                  [ "nat" ]
                  ( TmIndType "nat" [])
                  [ Equation
                    [ "O" ]
                    ( TmRel "y" 0 )
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
                        , TmRel "y" 1 ]])]))))))
      `shouldBe`
      Right
      ( Def "plus"
        ( TmProd "x"
          ( TmIndType "nat" [] )
          ( TmProd "y"
            ( TmIndType "nat" [] )
            ( TmIndType "nat" [] )))
        ( TmFix 1
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
                ( TmMatch 0
                  ( TmRel "x" 1 )
                  "x0"
                  [ "nat" ]
                  ( TmIndType "nat" [])
                  [ Equation
                    [ "O" ]
                    ( TmRel "y" 0 )
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
                        , TmRel "y" 1 ]])]))))))
    it "Ind" $
      computeDecParamCmd
      ( Ind "T" 1
        ( TmProd "x"
          ( TmIndType "nat" [])
          ( TmProd "_"
            ( TmIndType "nat" [])
              TmType ))
        ( TmLambda "x"
          ( TmIndType "nat" [])
          ( TmLambda ".0"
            ( TmIndType "nat" [])
            ( TmIndType "T"
              [ TmRel "x" 1
              , TmRel ".0" 0 ])))
        [ ( "X"
          , TmProd "x"
            ( TmIndType "nat" [])
            ( TmProd "y"
              ( TmIndType "nat" [])
              ( TmProd "_"
                ( TmAppl
                  [ TmLambda "a"
                      TmType
                    ( TmLambda ".0"
                      ( TmRel "a" 0 )
                      ( TmLambda ".1"
                        ( TmRel "a" 1 )
                        ( TmIndType "eq"
                          [ TmRel "a" 2
                          , TmRel ".0" 1
                          , TmRel ".1" 0 ])))
                  , TmIndType "nat" []
                  , TmAppl
                    [ TmFix (-1)
                      ( TmLambda "plus"
                        ( TmProd "t"
                          ( TmIndType "nat" [])
                          ( TmProd "y"
                            ( TmIndType "nat" [])
                            ( TmIndType "nat" [])))
                        ( TmLambda "t"
                          ( TmIndType "nat" [])
                          ( TmLambda "y"
                            ( TmIndType "nat" [])
                            ( TmMatch 0
                              ( TmRel "t" 1 )
                              "t0"
                              [ "nat" ]
                              ( TmIndType "nat" [])
                              [ Equation
                                [ "O" ]
                                ( TmRel "y" 0 )
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
                                    , TmRel "y" 1 ]])]))))
                    , TmRel "x" 1
                    , TmRel "y" 0 ]
                  , TmConstr "O" []])
                ( TmIndType "T"
                  [ TmRel "x" 2
                  , TmRel "y" 1 ])))
          , TmLambda "x"
            ( TmIndType "nat" [])
            ( TmLambda "y"
              ( TmIndType "nat" [])
              ( TmLambda ".0"
                ( TmAppl
                  [ TmLambda "a"
                      TmType
                    ( TmLambda ".0"
                      ( TmRel "a" 0 )
                      ( TmLambda ".1"
                        ( TmRel "a" 1 )
                        ( TmIndType "eq"
                          [ TmRel "a" 2
                          , TmRel ".0" 1
                          , TmRel ".1" 0 ])))
                  , TmIndType "nat" []
                  , TmAppl
                    [ TmFix (-1)
                      ( TmLambda "plus"
                        ( TmProd "t"
                          ( TmIndType "nat" [])
                          ( TmProd "y"
                            ( TmIndType "nat" [])
                            ( TmIndType "nat" [])))
                        ( TmLambda "t"
                          ( TmIndType "nat" [])
                          ( TmLambda "y"
                            ( TmIndType "nat" [])
                            ( TmMatch 0
                              ( TmRel "t" 1 )
                              "t0"
                              [ "nat" ]
                              ( TmIndType "nat" [])
                              [ Equation
                                [ "O" ]
                                ( TmRel "y" 0 )
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
                                    , TmRel "y" 1 ]])]))))
                    , TmRel "x" 1
                    , TmRel "y" 0 ]
                  , TmConstr "O" []])
                ( TmConstr "X"
                  [ TmRel "x" 2
                  , TmRel "y" 1
                  , TmRel ".0" 0 ]))))])
      `shouldBe`
      Right
      ( Ind "T" 1
        ( TmProd "x"
          ( TmIndType "nat" [])
          ( TmProd "_"
            ( TmIndType "nat" [])
              TmType ))
        ( TmLambda "x"
          ( TmIndType "nat" [])
          ( TmLambda ".0"
            ( TmIndType "nat" [])
            ( TmIndType "T"
              [ TmRel "x" 1
              , TmRel ".0" 0 ])))
        [ ( "X"
          , TmProd "x"
            ( TmIndType "nat" [])
            ( TmProd "y"
              ( TmIndType "nat" [])
              ( TmProd "_"
                ( TmAppl
                  [ TmLambda "a"
                      TmType
                    ( TmLambda ".0"
                      ( TmRel "a" 0 )
                      ( TmLambda ".1"
                        ( TmRel "a" 1 )
                        ( TmIndType "eq"
                          [ TmRel "a" 2
                          , TmRel ".0" 1
                          , TmRel ".1" 0 ])))
                  , TmIndType "nat" []
                  , TmAppl
                    [ TmFix 1
                      ( TmLambda "plus"
                        ( TmProd "t"
                          ( TmIndType "nat" [])
                          ( TmProd "y"
                            ( TmIndType "nat" [])
                            ( TmIndType "nat" [])))
                        ( TmLambda "t"
                          ( TmIndType "nat" [])
                          ( TmLambda "y"
                            ( TmIndType "nat" [])
                            ( TmMatch 0
                              ( TmRel "t" 1 )
                              "t0"
                              [ "nat" ]
                              ( TmIndType "nat" [])
                              [ Equation
                                [ "O" ]
                                ( TmRel "y" 0 )
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
                                    , TmRel "y" 1 ]])]))))
                    , TmRel "x" 1
                    , TmRel "y" 0 ]
                  , TmConstr "O" []])
                ( TmIndType "T"
                  [ TmRel "x" 2
                  , TmRel "y" 1 ])))
          , TmLambda "x"
            ( TmIndType "nat" [])
            ( TmLambda "y"
              ( TmIndType "nat" [])
              ( TmLambda ".0"
                ( TmAppl
                  [ TmLambda "a"
                      TmType
                    ( TmLambda ".0"
                      ( TmRel "a" 0 )
                      ( TmLambda ".1"
                        ( TmRel "a" 1 )
                        ( TmIndType "eq"
                          [ TmRel "a" 2
                          , TmRel ".0" 1
                          , TmRel ".1" 0 ])))
                  , TmIndType "nat" []
                  , TmAppl
                    [ TmFix 1
                      ( TmLambda "plus"
                        ( TmProd "t"
                          ( TmIndType "nat" [])
                          ( TmProd "y"
                            ( TmIndType "nat" [])
                            ( TmIndType "nat" [])))
                        ( TmLambda "t"
                          ( TmIndType "nat" [])
                          ( TmLambda "y"
                            ( TmIndType "nat" [])
                            ( TmMatch 0
                              ( TmRel "t" 1 )
                              "t0"
                              [ "nat" ]
                              ( TmIndType "nat" [])
                              [ Equation
                                [ "O" ]
                                ( TmRel "y" 0 )
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
                                    , TmRel "y" 1 ]])]))))
                    , TmRel "x" 1
                    , TmRel "y" 0 ]
                  , TmConstr "O" []])
                ( TmConstr "X"
                  [ TmRel "x" 2
                  , TmRel "y" 1
                  , TmRel ".0" 0 ]))))])
    it "Fix" $
      computeDecParamCmd
      ( Fix "plus"
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
                  ( TmMatch 0
                    ( TmRel "x" 1 )
                    "x0"
                    [ "nat" ]
                    ( TmIndType "nat" [])
                    [ Equation
                      [ "O" ]
                      ( TmRel "y" 0 )
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
                          , TmRel "y" 1 ]])]))))))
      `shouldBe`
      Right
      ( Fix "plus"
          ( TmFix 1
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
                  ( TmMatch 0
                    ( TmRel "x" 1 )
                    "x0"
                    [ "nat" ]
                    ( TmIndType "nat" [])
                    [ Equation
                      [ "O" ]
                      ( TmRel "y" 0 )
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
                          , TmRel "y" 1 ]])]))))))

