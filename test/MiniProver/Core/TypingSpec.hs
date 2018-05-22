module MiniProver.Core.TypingSpec (main, spec) where

import MiniProver.Core.Typing
import MiniProver.Core.Syntax
import MiniProver.Core.Context
import MiniProver.Utils.ContextForTesting
import Test.Hspec

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
  describe "simplifyType" $ do
    it "simple" $
      simplifyType
      ( TmAppl
        [ TmLambda "x"
            TmType
          ( TmRel "x" 0 )
        , TmIndType "nat" [] ])
      `shouldBe`
      TmIndType "nat" []
    it "nested" $
      simplifyType
      ( TmAppl
        [ TmLambda "f"
          ( TmProd "_"
            TmType
            TmType)
          ( TmLambda "x"
            TmType
            ( TmAppl
              [ TmRel "f" 1
              , TmRel "x" 0 ]))
        , TmLambda "x"
          TmType
          ( TmRel "x" 0 )
        , TmIndType "nat" [] ])
      `shouldBe`
      TmIndType "nat" []
    it "nested-2" $
      simplifyType
      ( TmProd "A"
          TmType
        ( TmAppl
          [ TmLambda "x"
              TmType
            ( TmRel "x" 0 )
          , TmRel "A" 0 ]))
      `shouldBe`
      TmProd "A"
        TmType
      ( TmRel "A" 0 )
  describe "typeof" $ do
    describe "TmRel" $
      it "plus" $
        typeof natContext (TmRel "plus" 0) `shouldBe`
          Right
          ( TmProd "a"
            ( TmIndType "nat" [] )
            ( TmProd "b"
              ( TmIndType "nat" [] )
              ( TmIndType "nat" [] )))
    describe "TmAppl" $ do
      it "plus 1 2" $
        typeof natContextWithPredefinedNumbers
          ( TmAppl
            [ TmRel "plus" 3
            , TmRel "one" 1
            , TmRel "two" 2 ])
          `shouldBe`
          Right
            ( TmIndType "nat" [] )
      it "partial -- plus 1" $
        typeof natContextWithPredefinedNumbers 
          ( TmAppl
            [ TmRel "plus" 3
            , TmRel "one" 1 ])
          `shouldBe`
          Right
          ( TmProd "b"
              ( TmIndType "nat" [] )
              ( TmIndType "nat" [] ))
    describe "TmProd" $
      it "simple" $
        typeof natContextWithPredefinedNumbers
          ( TmProd "a"
            ( TmIndType "nat" [] )
            ( TmProd "b"
              ( TmIndType "nat" [] )
              ( TmIndType "nat" [] )))
        `shouldBe`
        Right TmType
    describe "TmLambda" $ do
      it "simple" $
        typeof natContextWithPredefinedNumbers
          ( TmLambda "x"
            ( TmIndType "nat" [] )
            ( TmAppl 
              [ TmRel "plus" 4
              , TmRel "one" 2
              , TmRel "x" 0 ]))
        `shouldBe`
        Right
        ( TmProd "x"
          ( TmIndType "nat" [] )
          ( TmIndType "nat" [] ))
      it "simple-2" $
        -- Definition cons2 (T:Type) (a:T) (b:T) (ls:list T) : list T := cons T a (cons T b ls).
        typeof listContext
          ( TmLambda "T" 
              TmType 
            ( TmLambda "a" 
              ( TmRel "T" 0 )
              ( TmLambda "b" 
                ( TmRel "T" 1 )
                ( TmLambda "ls"
                  ( TmAppl 
                    [ TmLambda "T" 
                        TmType 
                      ( TmIndType "list" 
                        [ TmRel "T" 0 ])
                    , TmRel "T" 2 ])
                  ( TmAppl 
                    [ TmLambda "T" 
                        TmType 
                      ( TmLambda ".0" 
                        ( TmRel "T" 0 )
                        ( TmLambda ".1"
                          ( TmIndType "list" 
                            [ TmRel "T" 1 ])
                          ( TmConstr "cons" 
                            [ TmRel "T" 2
                            , TmRel ".0" 1
                            , TmRel ".1" 0 ])))
                    , TmRel "T" 3
                    , TmRel "a" 2
                    , TmAppl 
                      [ TmLambda "T" 
                          TmType 
                        ( TmLambda ".0" 
                          ( TmRel "T" 0 )
                          ( TmLambda ".1" 
                            ( TmIndType "list" 
                              [ TmRel "T" 1 ])
                            ( TmConstr "cons"
                              [ TmRel "T" 2
                              , TmRel ".0" 1
                              , TmRel ".1" 0 ])))
                      , TmRel "T" 3
                      , TmRel "b" 1
                      , TmRel "ls" 0]])))))
        `shouldBe`
        Right
        ( TmProd "T"
            TmType
            ( TmProd "a"
              ( TmRel "T" 0 )
              ( TmProd "b"
                ( TmRel "T" 1 )
                ( TmProd "ls"
                  ( TmAppl 
                    [ TmLambda "T" 
                        TmType 
                      ( TmIndType "list" 
                        [ TmRel "T" 0 ])
                    , TmRel "T" 2 ])
                  ( TmIndType "list"
                    [ TmRel "T" 3 ])))))
    describe "TmFix" $
      it "fix plus" $
      -- fix plus (x:nat) (y:nat):nat:=
      --   match x in nat return nat with
      --   | O => y
      --   | S xx => plus xx (S y) 
      --   end
        typeof natContext
          ( TmFix (-1)
            ( TmLambda "plus"
              ( TmProd "x"
                ( TmIndType "nat" [] )
                ( TmProd "y"
                  ( TmIndType "nat" [] )
                  ( TmIndType "nat" [] )))
              (TmLambda "x"
                ( TmIndType "nat" [] )
                (TmLambda "y"
                  ( TmIndType "nat" [] )
                  (TmMatch
                    ( TmRel "x" 1 )
                    [ "nat" ]
                    ( TmIndType "nat" [] )
                    [ Equation ["O"]
                        ( TmRel "y" 0 )
                    , Equation ["S", "xx"]
                        (TmAppl
                          [ TmRel "plus" 3
                          , TmRel "xx" 0
                          , TmConstr "S"
                            [ TmRel "y" 1 ]])])))))
          `shouldBe`
          Right
          ( TmProd "x"
            ( TmIndType "nat" [] )
            ( TmProd "y"
              ( TmIndType "nat" [] )
              ( TmIndType "nat" [] )))
    describe "TmLetIn" $
      it "simple" $
        typeof natContextWithPredefinedNumbers
          (TmLetIn "f" 
            ( TmProd "x"
              ( TmIndType "nat" [] )
              ( TmIndType "nat" [] ))
            ( TmLambda "x"
              ( TmIndType "nat" [] )
              ( TmAppl
                [ TmRel "plus" 4
                , TmRel "x" 0
                , TmRel "one" 2 ]))
            ( TmAppl
              [ TmRel "plus" 4
              , TmRel "two" 3
              , TmAppl
                [ TmRel "f" 0
                , TmRel "one" 2 ]]))
          `shouldBe`
          Right
          ( TmIndType "nat" [] )
    describe "TmIndType" $
      it "simple" $
        typeof natContextWithPredefinedNumbers
          ( TmIndType "nat" [] )
        `shouldBe`
        Right TmType
    describe "TmConstr" $ do
      it "simple-1" $
        typeof natContextWithPredefinedNumbers
          ( TmConstr "O" [] )
        `shouldBe`
        Right ( TmIndType "nat" [] )
      it "simple-2" $
        typeof natContextWithPredefinedNumbers
          ( TmConstr "S"
            [ TmConstr "O" [] ])
        `shouldBe`
        Right ( TmIndType "nat" [] )
    describe "TmMatch" $ do
      it "non-dependent" $
        typeof natContextWithPredefinedNumbers
        ( TmMatch
          ( TmRel "one" 1 )
          [ "nat" ]
          ( TmIndType "nat" [] )
          [ Equation ["O"]
              ( TmRel "zero" 0 )
          , Equation ["S", "xx"]
              ( TmRel "xx" 0 )])
        `shouldBe`
        Right ( TmIndType "nat" [] )
      it "dependent" $
        typeof natContextWithPredefinedNumbers
        ( TmLambda "x"
          ( TmIndType "nat" [] )
          ( TmMatch
            ( TmRel "x" 0 )
            [ "nat" ]
            ( TmIndType "eq"
              [ TmIndType "nat" []
              , TmRel "x" 0
              , TmRel "x" 0 ])
            [ Equation ["O"]
              ( TmConstr "eqrefl"
                [ TmIndType "nat" []
                , TmRel "x" 0 ])
            , Equation ["S", "n"]
              ( TmConstr "eqrefl"
                [ TmIndType "nat" []
                , TmRel "n" 0 ])]))
        `shouldBe`
        Right 
        ( TmProd "x"
          ( TmIndType "nat" [] )
          ( TmIndType "eq"
            [ TmIndType "nat" []
            , TmRel "x" 0
            , TmRel "x" 0 ]))
      it "f_equal" $
        typeof natContextWithPredefinedNumbers
        ( TmLambda "A"
          TmType
          ( TmLambda "B"
            TmType
            ( TmLambda "f"
              ( TmProd "_"
                ( TmRel "A" 1 )
                ( TmRel "B" 1 ))
              ( TmLambda "x"
                ( TmRel "A" 2 )
                ( TmLambda "y"
                  ( TmRel "A" 3 )
                  ( TmLambda "H"
                    ( TmIndType "eq"
                      [ TmRel "A" 4, TmRel "x" 1, TmRel "y" 0 ])
                    ( TmMatch
                      ( TmRel "H" 0 )
                      [ "eq1", "t", "x0", "y0" ]
                      ( TmIndType "eq1"
                        [ TmRel "B" 7
                        , TmAppl
                          [ TmRel "f" 6
                          , TmRel "x0" 1 ]
                        , TmAppl
                          [ TmRel "f" 6
                          , TmRel "y0" 0 ]])
                      [ Equation ["eqrefl", "t", "x0"]
                        ( TmConstr "eqrefl"
                          [ TmRel "B" 6
                          , TmAppl
                            [ TmRel "f" 5
                            , TmRel "x0" 0 ]])])))))))
        `shouldBe`
        Right
        ( TmProd "A"
          TmType
          ( TmProd "B"
            TmType
            ( TmProd "f"
              ( TmProd "_"
                ( TmRel "A" 1 )
                ( TmRel "B" 1 ))
              ( TmProd "x"
                ( TmRel "A" 2 )
                ( TmProd "y"
                  ( TmRel "A" 3 )
                  ( TmProd "H"
                    ( TmIndType "eq"
                      [ TmRel "A" 4, TmRel "x" 1, TmRel "y" 0 ])
                    ( TmIndType "eq"
                      [ TmRel "B" 4
                      , TmAppl
                        [ TmRel "f" 3
                        , TmRel "x" 2 ]
                      , TmAppl
                        [ TmRel "f" 3
                        , TmRel "y" 1 ]])))))))
    describe "lzw_TmLambda" $ 
      it "" $
        typeof [("A",TmAbbBind (TmTypeHigher) (Just TmType))] 
          (TmLambda
            "x"
            (TmRel "A" 0)
            (TmLambda
              "y"
              (TmRel "x" 0)
              (TmLambda
                "z"
                (TmRel "y" 0)
                (TmRel "z" 0)))) 
        `shouldBe` 
          Right 
          (TmProd     
            "x"
            (TmRel "A" 0)
            (TmProd  
              "y"
              (TmRel "x" 0)
              (TmProd   
                "z"
                (TmRel "y" 0)
                (TmRel "y" 1))))
    describe "lzw_Prod" $
      it "" $
        typeof [] 
          (TmProd
            "x"
            (TmType)
            (TmProd
              "y"
              (TmType)
              (TmRel "x" 1)))
        `shouldBe` 
          Right TmType
    describe "lzw_TmFix" $
      it "" $
        typeof []
          (TmFix (-1)
            (TmLambda
              "f"
              (TmProd
                "x"
                (TmType)
                (TmProd
                  "y"
                  (TmProd
                    "_"
                    (TmType)
                    (TmType))
                  (TmAppl
                    [TmRel "y" 0,
                     (TmAppl
                       [TmRel "y" 0,
                        TmRel "x" 1])])))
                (TmLambda
                  "x"
                  (TmType)
                  (TmLambda
                    "y"
                    (TmType)
                    (TmLambda
                      "z"
                      (TmType)
                      (TmRel "x" 2))))))
        `shouldBe`
          Right 
          (TmProd
            "x"
            (TmType)
            (TmProd
              "y"
              (TmProd
                "_"
                (TmType)
                (TmType))
              (TmAppl
                [TmRel "y" 0,
                  (TmAppl
                    [TmRel "y" 0,
                    TmRel "x" 1])])))
    describe "lzw_TmLetIn" $
      it "" $
        typeof natContextWithPredefinedNumbers
        ( TmLetIn "x"
            ( TmIndType "nat" [])
            ( TmRel "zero" 2 )
            ( TmLetIn "y"
              ( TmIndType "nat" [])
              ( TmRel "zero" 3 )
              ( TmLetIn "z"
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
                  , TmRel "y" 0
                  , TmRel "x" 1 ])
                ( TmAppl
                  [ TmLambda "a"
                      TmType
                    ( TmLambda "x"
                      ( TmRel "a" 0 )
                      ( TmConstr "eqrefl"
                        [ TmRel "a" 1
                        , TmRel "x" 0 ]))
                  , TmIndType "nat" []
                  , TmRel "zero" 4 ])
                ( TmAppl
                  [ TmLambda "a"
                      TmType
                    ( TmLambda "x"
                      ( TmRel "a" 0 )
                      ( TmConstr "eqrefl"
                        [ TmRel "a" 1
                        , TmRel "x" 0 ]))
                  , TmIndType "nat" []
                  , TmRel "x" 2 ]))))
        `shouldBe` 
          Right 
          (TmIndType
            "eq"
            [
              (TmIndType "nat" []),
              (TmRel "zero" 0),
              (TmRel "zero" 0)])
    describe "lzw_IndType" $
      it "" $
        typeof (listContext ++ natContextWithPredefinedNumbers)
          (TmIndType 
            "list"
            [
              TmIndType "nat" []
            ])
        `shouldBe`
          Right TmType
    describe "lzw_Constr" $
      it "" $
        typeof (listContext ++ natContextWithPredefinedNumbers)
          (TmConstr
            "cons"
            [
              (TmIndType "nat" []),
              (TmRel "zero" 1),
              (TmConstr
                "cons"
                [
                  (TmIndType "nat" []),
                  (TmRel "one" 2),
                  (TmConstr
                    "cons"
                    [
                      (TmIndType "nat" []),
                      (TmRel "two" 3),
                      (TmConstr
                        "nil"
                        [
                          (TmIndType "nat" [])
                        ])
                    ])
                ])
            ])
        `shouldBe` 
           Right 
           (TmIndType
             "list"
             [
               TmIndType "nat" []
             ])





{-
    describe "lzw_Error" $ do
      it "rel not exist" $
        typeof 
          [] 
          (TmRel "x" 0)
        `shouldBe`
        Left 
        (TypingError 
          (TmRel "x" 0) 
          "There is no such bind")
      it "rel is a NameBind" $
        typeof 
          [(NameBind "x")] 
          (TmRel "x" 0)
      `shouldBe`
        Left 
        (TypingError 
          (TmRel "x" 0) 
          "NameBind is not a type.") 
      it "apply is not a func" $
        typeof 
          [(VarBind "x" TmType)] 
          (TmAppl [(TmRel "x" 0)])
        `shouldBe`
        Left 
        (TypingError
          (TmRel "x" 0)
          "")
-}