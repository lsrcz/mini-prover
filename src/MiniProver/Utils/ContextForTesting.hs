module MiniProver.Utils.ContextForTesting where

import MiniProver.Core.Syntax
import MiniProver.Core.Context

simpleContext :: Context
simpleContext = [("A", NameBind), ("B", NameBind), ("C", NameBind), ("D", NameBind)]

natContext :: Context
natContext =  
  [ ( "plus"
    , TmAbbBind
      ( TmProd "a"
        ( TmIndType "nat" [] )
        ( TmProd "b"
          ( TmIndType "nat" [] )
          ( TmIndType "nat" [] )))
      ( Just
        ( TmFix 1
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
                      [ TmLambda ".0"
                          ( TmIndType "nat" [] )
                          ( TmConstr "S" [ TmRel ".0" 0 ])
                      , TmAppl
                        [ TmRel "plus" 3
                        , TmRel "n" 0
                        , TmRel "b" 1 ]])])))))))
  , ( "nat"
    , IndTypeBind 0
      TmType
      ( TmIndType "nat" [] )
      [ Constructor "O"
        ( TmIndType "nat" [] )
        ( TmConstr "O" [] )
      , Constructor "S"
        ( TmProd "_"
          ( TmIndType "nat" [] )
          ( TmIndType "nat" [] ))
        (TmLambda ".0"
          ( TmIndType "nat" [] )
          ( TmConstr "S" [ TmRel ".0" 0 ]))])
  , ( "eq"
    , IndTypeBind 1
      ( TmProd "a"
        TmType
        ( TmProd "_"
          ( TmRel "a" 0 )
          ( TmProd "_"
            ( TmRel "a" 1 )
            TmType )))
      ( TmLambda "a"
        TmType
        ( TmLambda ".0"
          ( TmRel "a" 0 )
          ( TmLambda ".1" 
            ( TmRel "a" 1 )
            ( TmIndType "eq"
              [ TmRel "a" 2, TmRel ".0" 1, TmRel ".1" 0 ]))))
      [ Constructor "eqrefl"
        ( TmProd "a"
          TmType
          ( TmProd "x"
            ( TmRel "a" 0 )
            ( TmIndType "eq"
              [ TmRel "a" 1, TmRel "x" 0, TmRel "x" 0 ])))
        ( TmLambda "a" 
          TmType
          ( TmLambda "x"
            ( TmRel "a" 0 )
            ( TmConstr "eqrefl"
              [ TmRel "a" 1, TmRel "x" 0 ])))])]

natContextWithPredefinedNumbers :: Context
natContextWithPredefinedNumbers =
  [ ( "two"
    , TmAbbBind
      ( TmIndType "nat" [] )
      ( Just
        ( TmConstr "S"
          [ TmRel "one" 0 ])))
  , ( "one"
    , TmAbbBind
      ( TmIndType "nat" [] )
      ( Just
        ( TmConstr "S"
          [ TmRel "zero" 0 ])))
  , ( "zero"
    , TmAbbBind
      ( TmIndType "nat" [] )
      ( Just
        ( TmConstr "O" [] )))
            
            ] ++ natContext

natContextWithPredefinedFunctions :: Context
natContextWithPredefinedFunctions =
  [ ( "plusThreeNumbers"
    , TmAbbBind
      ( TmProd "x"
        ( TmIndType "nat" [] )
        ( TmProd "y"
          ( TmIndType "nat" [] )
          ( TmProd "z"
            ( TmIndType "nat" [] )
            ( TmIndType "nat" [] ))))
      ( Just $ TmLambda "x"
        ( TmIndType "nat" [] )
        ( TmLambda "y"
          ( TmIndType "nat" [] )
          ( TmLambda "z"
            ( TmIndType "nat" [] )
            ( TmAppl
              [ TmRel "plus" 11
              , TmRel "x" 2
              , TmAppl
                [ TmRel "plus" 11
                , TmRel "y" 1
                , TmRel "z" 0 ]])))))
  , ( "succByPlus"
    , TmAbbBind
      ( TmProd "x"
        ( TmIndType "nat" [] )
        ( TmIndType "nat" [] ))
      ( Just $ TmAppl
        [ TmRel "plus" 7
        , TmAppl
          [ TmLambda ".0"
            ( TmIndType "nat" [] )
            ( TmConstr "S"
              [ TmRel ".0" 0 ])
          , TmConstr "O" [] ]]))
  , ( "succthreeLetIn"
    , TmAbbBind
      ( TmProd "x"
        ( TmIndType "nat" [] )
        ( TmIndType "nat" [] ))
      ( Just $ TmLambda "x"
        ( TmIndType "nat" [] )
        ( TmLetIn "y"
          ( TmIndType "nat" [] )
          ( TmAppl
            [ TmRel "succtwo" 1
            , TmRel "x" 0 ])
          ( TmAppl
            [ TmRel "succ" 3
            , TmRel "y" 0 ]))))
  ,( "succtwo"
    , TmAbbBind
      ( TmProd "x"
        ( TmIndType "nat" [] )
        ( TmIndType "nat" [] ))
      ( Just $ TmLambda "x"
        ( TmIndType "nat" [] )
        ( TmAppl
          [ TmRel "succ" 1
          , TmAppl
            [ TmRel "succ" 1
            , TmRel "x" 0 ]])))
  , ( "succ"
    , TmAbbBind
      ( TmProd "x"
        ( TmIndType "nat" [] )
        ( TmIndType "nat" [] ))
      ( Just $ TmLambda "x"
        ( TmIndType "nat" [] )
        ( TmAppl
          [ TmLambda ".0"
            ( TmIndType "nat" [] )
            ( TmConstr "S" [ TmRel ".0" 0 ])
          , TmRel "x" 0 ])))
  , ( "pred"
    , TmAbbBind
      ( TmProd "x"
        ( TmIndType "nat" [] )
        ( TmIndType "nat" [] ))
      ( Just $ TmLambda "x"
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
            ( TmRel "n" 0 )])))] ++ natContextWithPredefinedNumbers

natContextWithAxiom :: Context
natContextWithAxiom =
  ( "pluscomm"
  , TmAbbBind
    ( TmProd "x"
      ( TmIndType "nat" [] )
      ( TmProd "y"
        ( TmIndType "nat" [] )
        ( TmIndType "eq"
          [ TmIndType "nat" []
          , TmAppl
            [ TmRel "plus" 2
            , TmRel "x" 1
            , TmRel "y" 0 ]
          , TmAppl
            [ TmRel "plus" 2
            , TmRel "y" 0
            , TmRel "x" 1 ]])))
      Nothing ) : natContext

listContext :: Context
listContext =
  [ ( "list"
    , IndTypeBind 1
      ( TmProd "T"
        TmType
        TmType )
      ( TmLambda "T"
        TmType
        ( TmIndType "list"
          [ TmRel "T" 0 ]))
      [ Constructor "nil"
        ( TmProd "T"
          TmType
          ( TmIndType "list"
            [ TmRel "T" 0 ]))
        ( TmLambda "T"
          TmType
          ( TmConstr "nil"
            [ TmRel "T" 0 ]))
      , Constructor "cons"
        ( TmProd "T"
          TmType
          ( TmProd "_"
            ( TmRel "T" 0 )
            ( TmProd "_"
              ( TmIndType "list"
                [ TmRel "T" 1 ])
              ( TmIndType "list"
                [ TmRel "T" 2 ]))))
        ( TmLambda "T"
          TmType
          ( TmLambda ".0"
            ( TmRel "T" 0 )
            ( TmLambda ".1"
              ( TmIndType "list"
                [ TmRel "T" 1 ])
              ( TmConstr "cons"
                [ TmRel "T" 2, TmRel ".0" 1, TmRel ".1" 0 ]))))])]

ilistContext :: Context
ilistContext =
  ( "ilist"
  , IndTypeBind 1
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
    [ Constructor "inil"
      ( TmProd "T"
          TmType
        ( TmIndType "ilist"
          [ TmRel "T" 0
          , TmConstr "O" []]))
      ( TmLambda "T"
          TmType
        ( TmConstr "inil"
          [ TmRel "T" 0 ]))
    , Constructor "icons"
      ( TmProd "T"
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
                  , TmRel "n" 2 ]])))))
      (TmLambda "T"
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
                , TmRel ".1" 0 ])))))]) : natContext

natListContext :: Context
natListContext = 
  ( "natList"
  , IndTypeBind 0
    TmType
    ( TmIndType "natList" [])
    [ Constructor "natNil"
      ( TmIndType "natList" [] )
      ( TmConstr "natNil" [] )
    , Constructor "natCons"
      ( TmProd ".0"
        ( TmIndType "nat" [] )
        ( TmProd ".1"
          ( TmIndType "natList" [] )
          ( TmIndType "natList" [] )))
      ( TmLambda ".0"
        ( TmIndType "nat" [] )
        ( TmLambda ".1"
          ( TmIndType "natList" [] )
          ( TmConstr "natCons" [TmRel ".0" 1, TmRel ".1" 0])))]) : natContext

dependentContext :: Context
dependentContext =
  [ ( "A", VarBind ( TmRel "B" 0 ))
  , ( "B", VarBind ( TmRel "C" 1 ))
  , ( "x", NameBind )
  , ( "C", TmAbbBind
           ( TmRel "D" 0 )
           ( Just $ TmRel "E" 1 ))
  , ( "D", NameBind )
  , ( "E", NameBind )]

nestedPosContext :: Context
nestedPosContext =
  [ ( "t1"
    , IndTypeBind 1
      ( TmProd "T"
          TmType
        ( TmProd "_"
            TmType
            TmType ))
      ( TmLambda "T"
          TmType
        ( TmLambda ".0"
            TmType
          ( TmIndType "t1"
            [ TmRel "T" 1
            , TmRel ".0" 0 ])))
      [ Constructor "t11"
        ( TmProd "T"
            TmType
          ( TmIndType "t1"
            [ TmRel "T" 0
            , TmRel "T" 0 ]))
        ( TmLambda "T"
            TmType
          ( TmConstr "t11"
            [ TmRel "T" 0 ]))])
  , ( "t2"
    , IndTypeBind 1
      ( TmProd "T"
          TmType
        ( TmProd "_"
            TmType
            TmType ))
      ( TmLambda "T"
          TmType
        ( TmLambda ".0"
            TmType
          ( TmIndType "t2"
            [ TmRel "T" 1
            , TmRel ".0" 0 ])))
      [ Constructor "t21"
        ( TmProd "T"
            TmType
          ( TmProd "x"
              TmType
            ( TmIndType "t2"
              [ TmRel "T" 1
              , TmRel "x" 0 ])))
        ( TmLambda "T"
            TmType
          ( TmLambda "x"
              TmType
            ( TmConstr "t21"
              [ TmRel "T" 1
              , TmRel "x" 0 ])))])] ++ natContext


-- real world context
realTrueContext :: Context
realTrueContext =
  [ ( "True_rect"
    , TmAbbBind
      ( TmProd "P"
        ( TmProd "_"
          ( TmIndType "True" [])
            TmType )
        ( TmProd "f"
          ( TmAppl
            [ TmRel "P" 0
            , TmConstr "I" []])
          ( TmProd "t"
            ( TmIndType "True" [])
            ( TmAppl
              [ TmRel "P" 2
              , TmRel "t" 0 ]))))
      ( Just
        ( TmLambda "P"
          ( TmProd "_"
            ( TmIndType "True" [])
              TmType )
          ( TmLambda "f"
            ( TmAppl
              [ TmRel "P" 0
              , TmConstr "I" []])
            ( TmLambda "t"
              ( TmIndType "True" [])
              ( TmMatch 0
                ( TmRel "t" 0 )
                  "T"
                [ "True" ]
                ( TmAppl
                  [ TmRel "P" 3
                  , TmRel "T" 0 ])
                [ Equation
                  [ "I" ]
                  ( TmRel "f" 1 )]))))))
  , ( "True"
    , IndTypeBind 0
        TmType
      ( TmIndType "True" [])
      [ Constructor "I"
        ( TmIndType "True" [] )
        ( TmConstr "I" [] )])]

realFalseContext :: Context
realFalseContext =
  [ ( "False_rect"
    , TmAbbBind
      ( TmProd "P"
        ( TmProd "_"
          ( TmIndType "False" [])
            TmType )
        ( TmProd "f"
          ( TmIndType "False" [])
          ( TmAppl
            [ TmRel "P" 1
            , TmRel "f" 0 ])))
      ( Just
        ( TmLambda "P"
          ( TmProd "_"
            ( TmIndType "False" [])
              TmType )
          ( TmLambda "f"
            ( TmIndType "False" [])
            ( TmMatch 0
              ( TmRel "f" 0 )
                "F"
              [ "False" ]
              ( TmAppl
                [ TmRel "P" 2
                , TmRel "F" 0 ])
              [  ])))))
  , ( "False"
    , IndTypeBind 0
        TmType
      ( TmIndType "False" [] )
      [])] ++ realTrueContext

realEqContext :: Context
realEqContext =
  [ ( "eq_rect"
    , TmAbbBind
      ( TmProd "T"
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
              ( TmProd "t"
                ( TmRel "T" 3 )
                ( TmProd "e"
                  ( TmIndType "eq"
                    [ TmRel "T" 4
                    , TmRel "x" 3
                    , TmRel "t" 0 ])
                  ( TmAppl
                    [ TmRel "P" 3
                    , TmRel "t" 1
                    , TmRel "e" 0 ])))))))
        ( Just
          ( TmLambda "T"
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
                  ( TmLambda "t"
                    ( TmRel "T" 3 )
                    ( TmLambda "e"
                      ( TmIndType "eq"
                        [ TmRel "T" 4
                        , TmRel "x" 3
                        , TmRel "t" 0 ])
                      ( TmMatch 2
                        ( TmRel "e" 0 )
                          "e0"
                        [ "eq"
                        , "_"
                        , "_"
                        , "t0" ]
                        ( TmAppl
                          [ TmRel "P" 5
                          , TmRel "t0" 1
                          , TmRel "e0" 0 ])
                        [ Equation
                          [ "eq_refl"
                          , "_"
                          , "_" ]
                          ( TmRel "f" 2 )])))))))))
  , ( "eq"
    , IndTypeBind 2
      ( TmProd "T"
          TmType
        ( TmProd "x"
          ( TmRel "T" 0 )
          ( TmProd "_"
            ( TmRel "T" 1 )
              TmType )))
      ( TmLambda "T"
          TmType
        ( TmLambda "x"
          ( TmRel "T" 0 )
          ( TmLambda "t"
            ( TmRel "T" 1 )
            ( TmIndType "eq"
              [ TmRel "T" 2
              , TmRel "x" 1
              , TmRel "t" 0 ]))))
      [ Constructor "eq_refl"
        ( TmProd "T"
            TmType
          ( TmProd "x"
            ( TmRel "T" 0 )
            ( TmIndType "eq"
              [ TmRel "T" 1
              , TmRel "x" 0
              , TmRel "x" 0 ])))
        ( TmLambda "T"
            TmType
          ( TmLambda "x"
            ( TmRel "T" 0 )
            ( TmConstr "eq_refl"
              [ TmRel "T" 1
              , TmRel "x" 0 ])))])] ++ realFalseContext

realAndContext :: Context
realAndContext =
  [ ( "and_rect"
    , TmAbbBind
      ( TmProd "A"
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
                  , TmRel "a" 0 ]))))))
      ( Just
        ( TmLambda "A"
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
                      , "a0"
                      , "b" ]
                      ( TmAppl
                        [ TmRel "f" 3
                        , TmRel "a0" 1
                        , TmRel "b" 0 ])]))))))))
  , ( "and"
    , IndTypeBind 2
      ( TmProd "A"
          TmType
        ( TmProd "B"
            TmType
            TmType ))
      ( TmLambda "A"
          TmType
        ( TmLambda "B"
            TmType
          ( TmIndType "and"
            [ TmRel "A" 1
            , TmRel "B" 0 ])))
      [ Constructor "conj"
        ( TmProd "A"
            TmType
          ( TmProd "B"
              TmType
            ( TmProd "_"
              ( TmRel "A" 1 )
              ( TmProd "_"
                ( TmRel "B" 1 )
                ( TmIndType "and"
                  [ TmRel "A" 3
                  , TmRel "B" 2 ])))))
        ( TmLambda "A"
            TmType
          ( TmLambda "B"
              TmType
            ( TmLambda "a"
              ( TmRel "A" 1 )
              ( TmLambda "b"
                ( TmRel "B" 1 )
                ( TmConstr "conj"
                  [ TmRel "A" 3
                  , TmRel "B" 2
                  , TmRel "a" 1
                  , TmRel "b" 0 ])))))])] ++ realEqContext

realOrContext :: Context
realOrContext =
  [ ( "or_rect"
    , TmAbbBind
      ( TmProd "A"
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
                    , TmRel "o" 0 ])))))))
      ( Just
        ( TmLambda "A"
            TmType
          ( TmLambda "B"
              TmType
            ( TmLambda "P"
              ( TmProd "_"
                ( TmIndType "or"
                  [ TmRel "A" 1
                  , TmRel "B" 0 ])
                  TmType )
              ( TmLambda "f"
                ( TmProd "a"
                  ( TmRel "A" 2 )
                  ( TmAppl
                    [ TmRel "P" 1
                    , TmConstr "or_introl"
                      [ TmRel "A" 3
                      , TmRel "B" 2
                      , TmRel "a" 0 ]]))
                ( TmLambda "f0"
                  ( TmProd "b"
                    ( TmRel "B" 2 )
                    ( TmAppl
                      [ TmRel "P" 2
                      , TmConstr "or_intror"
                        [ TmRel "A" 4
                        , TmRel "B" 3
                        , TmRel "b" 0 ]]))
                  ( TmLambda "o"
                    ( TmIndType "or"
                      [ TmRel "A" 4
                      , TmRel "B" 3 ])
                    ( TmMatch 2
                      ( TmRel "o" 0 )
                        "o0"
                      [ "or"
                      , "_"
                      , "_" ]
                      ( TmAppl
                        [ TmRel "P" 4
                        , TmRel "o0" 0 ])
                      [ Equation
                        [ "or_introl"
                        , "_"
                        , "_"
                        , "a" ]
                        ( TmAppl
                          [ TmRel "f" 3
                          , TmRel "a" 0 ])
                      , Equation
                        [ "or_intror"
                        , "_"
                        , "_"
                        , "b" ]
                        ( TmAppl
                          [ TmRel "f0" 2
                          , TmRel "b" 0 ])])))))))))
  , ( "or"
    , IndTypeBind 2
      ( TmProd "A"
          TmType
        ( TmProd "B"
            TmType
            TmType ))
      ( TmLambda "A"
          TmType
        ( TmLambda "B"
            TmType
          ( TmIndType "or"
            [ TmRel "A" 1
            , TmRel "B" 0 ])))
      [ Constructor "or_introl"
        ( TmProd "A"
            TmType
          ( TmProd "B"
              TmType
            ( TmProd "_"
              ( TmRel "A" 1 )
              ( TmIndType "or"
                [ TmRel "A" 2
                , TmRel "B" 1 ]))))
        ( TmLambda "A"
            TmType
          ( TmLambda "B"
              TmType
            ( TmLambda "a"
              ( TmRel "A" 1 )
              ( TmConstr "or_introl"
                [ TmRel "A" 2
                , TmRel "B" 1
                , TmRel "a" 0 ]))))
      , Constructor "or_intror"
        ( TmProd "A"
            TmType
          ( TmProd "B"
              TmType
            ( TmProd "_"
              ( TmRel "B" 0 )
              ( TmIndType "or"
                [ TmRel "A" 2
                , TmRel "B" 1 ]))))
        ( TmLambda "A"
            TmType
          ( TmLambda "B"
              TmType
            ( TmLambda "b"
              ( TmRel "B" 0 )
              ( TmConstr "or_intror"
                [ TmRel "A" 2
                , TmRel "B" 1
                , TmRel "b" 0 ]))))])] ++ realAndContext

realNatContext :: Context
realNatContext =
  [ ( "nat_rect"
    , TmAbbBind
      ( TmProd "P"
        ( TmProd "_"
          ( TmIndType "nat" [])
            TmType )
        ( TmProd "f"
          ( TmAppl
            [ TmRel "P" 0
            , TmConstr "O" []])
          ( TmProd "f0"
            ( TmProd "n"
              ( TmIndType "nat" [])
              ( TmProd "_"
                ( TmAppl
                  [ TmRel "P" 2
                  , TmRel "n" 0 ])
                ( TmAppl
                  [ TmRel "P" 3
                  , TmConstr "S"
                    [ TmRel "n" 1 ]])))
            ( TmProd "n"
              ( TmIndType "nat" [])
              ( TmAppl
                [ TmRel "P" 3
                , TmRel "n" 0 ])))))
      ( Just
        ( TmLambda "P"
          ( TmProd "_"
            ( TmIndType "nat" [])
              TmType )
          ( TmLambda "f"
            ( TmAppl
              [ TmRel "P" 0
              , TmConstr "O" []])
            ( TmLambda "f0"
              ( TmProd "n"
                ( TmIndType "nat" [])
                ( TmProd "_"
                  ( TmAppl
                    [ TmRel "P" 2
                    , TmRel "n" 0 ])
                  ( TmAppl
                    [ TmRel "P" 3
                    , TmConstr "S"
                      [ TmRel "n" 1 ]])))
              ( TmFix 1
                ( TmLambda "F"
                  ( TmProd "n"
                    ( TmIndType "nat" [])
                    ( TmAppl
                      [ TmRel "P" 3
                      , TmRel "n" 0 ]))
                  ( TmLambda "n"
                    ( TmIndType "nat" [])
                    ( TmMatch 0
                      ( TmRel "n" 0 )
                        "n0"
                      [ "nat" ]
                      ( TmAppl
                        [ TmRel "P" 5
                        , TmRel "n0" 0 ])
                      [ Equation
                        [ "O" ]
                        ( TmRel "f" 3 )
                      , Equation
                        [ "S"
                        , "n0" ]
                        ( TmAppl
                          [ TmRel "f0" 3
                          , TmRel "n0" 0
                          , TmAppl
                            [ TmRel "F" 2
                            , TmRel "n0" 0 ]])])))))))))
  , ( "nat"
    , IndTypeBind 0
        TmType
      ( TmIndType "nat" [])
      [ Constructor "O"
        ( TmIndType "nat" [] )
        ( TmConstr "O" [])
      , Constructor "S"
        ( TmProd "_"
          ( TmIndType "nat" [])
          ( TmIndType "nat" []))
        ( TmLambda "n"
          ( TmIndType "nat" [])
          ( TmConstr "S"
            [ TmRel "n" 0 ]))])] ++ realOrContext

realNatlistContext :: Context
realNatlistContext =
  [ ( "natlist_rect"
    , TmAbbBind
      ( TmProd "P"
        ( TmProd "_"
          ( TmIndType "natlist" [])
            TmType )
        ( TmProd "f"
          ( TmAppl
            [ TmRel "P" 0
            , TmConstr "natnil" []])
          ( TmProd "f0"
            ( TmProd "n"
              ( TmIndType "nat" [])
              ( TmProd "n0"
                ( TmIndType "natlist" [])
                ( TmProd "_"
                  ( TmAppl
                    [ TmRel "P" 3
                    , TmRel "n0" 0 ])
                  ( TmAppl
                    [ TmRel "P" 4
                    , TmConstr "natcons"
                      [ TmRel "n" 2
                      , TmRel "n0" 1 ]]))))
            ( TmProd "n"
              ( TmIndType "natlist" [])
              ( TmAppl
                [ TmRel "P" 3
                , TmRel "n" 0 ])))))
      ( Just
        ( TmLambda "P"
          ( TmProd "_"
            ( TmIndType "natlist" [])
              TmType )
          ( TmLambda "f"
            ( TmAppl
              [ TmRel "P" 0
              , TmConstr "natnil" []])
            ( TmLambda "f0"
              ( TmProd "n"
                ( TmIndType "nat" [])
                ( TmProd "n0"
                  ( TmIndType "natlist" [])
                  ( TmProd "_"
                    ( TmAppl
                      [ TmRel "P" 3
                      , TmRel "n0" 0 ])
                    ( TmAppl
                      [ TmRel "P" 4
                      , TmConstr "natcons"
                        [ TmRel "n" 2
                        , TmRel "n0" 1 ]]))))
              ( TmFix 1
                ( TmLambda "F"
                  ( TmProd "n"
                    ( TmIndType "natlist" [])
                    ( TmAppl
                      [ TmRel "P" 3
                      , TmRel "n" 0 ]))
                  ( TmLambda "n"
                    ( TmIndType "natlist" [])
                    ( TmMatch 0
                      ( TmRel "n" 0 )
                        "n0"
                      [ "natlist" ]
                      ( TmAppl
                        [ TmRel "P" 5
                        , TmRel "n0" 0 ])
                      [ Equation
                        [ "natnil" ]
                        ( TmRel "f" 3 )
                      , Equation
                        [ "natcons"
                        , "n0"
                        , "n1" ]
                        ( TmAppl
                          [ TmRel "f0" 4
                          , TmRel "n0" 1
                          , TmRel "n1" 0
                          , TmAppl
                            [ TmRel "F" 3
                            , TmRel "n1" 0 ]])])))))))))
  , ( "natlist"
    , IndTypeBind 0
        TmType
      ( TmIndType "natlist" [])
      [ Constructor "natnil"
        ( TmIndType "natlist" [] )
        ( TmConstr "natnil" [])
      , Constructor "natcons"
        ( TmProd "_"
          ( TmIndType "nat" [])
          ( TmProd "_"
            ( TmIndType "natlist" [])
            ( TmIndType "natlist" [])))
        ( TmLambda "n"
          ( TmIndType "nat" [])
          ( TmLambda "n0"
            ( TmIndType "natlist" [])
            ( TmConstr "natcons"
              [ TmRel "n" 1
              , TmRel "n0" 0 ])))])] ++ realNatContext

realListContext :: Context
realListContext =
  [ ( "list_rect"
    , TmAbbBind
      ( TmProd "T"
          TmType
        ( TmProd "P"
          ( TmProd "_"
            ( TmIndType "list"
              [ TmRel "T" 0 ])
              TmType )
          ( TmProd "f"
            ( TmAppl
              [ TmRel "P" 0
              , TmConstr "nil"
                [ TmRel "T" 1 ]])
            ( TmProd "f0"
              ( TmProd "t"
                ( TmRel "T" 2 )
                ( TmProd "l"
                  ( TmIndType "list"
                    [ TmRel "T" 3 ])
                  ( TmProd "_"
                    ( TmAppl
                      [ TmRel "P" 3
                      , TmRel "l" 0 ])
                    ( TmAppl
                      [ TmRel "P" 4
                      , TmConstr "cons"
                        [ TmRel "T" 5
                        , TmRel "t" 2
                        , TmRel "l" 1 ]]))))
              ( TmProd "l"
                ( TmIndType "list"
                  [ TmRel "T" 3 ])
                ( TmAppl
                  [ TmRel "P" 3
                  , TmRel "l" 0 ]))))))
      ( Just
        ( TmLambda "T"
            TmType
          ( TmLambda "P"
            ( TmProd "_"
              ( TmIndType "list"
                [ TmRel "T" 0 ])
                TmType )
            ( TmLambda "f"
              ( TmAppl
                [ TmRel "P" 0
                , TmConstr "nil"
                  [ TmRel "T" 1 ]])
              ( TmLambda "f0"
                ( TmProd "t"
                  ( TmRel "T" 2 )
                  ( TmProd "l"
                    ( TmIndType "list"
                      [ TmRel "T" 3 ])
                    ( TmProd "_"
                      ( TmAppl
                        [ TmRel "P" 3
                        , TmRel "l" 0 ])
                      ( TmAppl
                        [ TmRel "P" 4
                        , TmConstr "cons"
                          [ TmRel "T" 5
                          , TmRel "t" 2
                          , TmRel "l" 1 ]]))))
                ( TmFix 1
                  ( TmLambda "F"
                    ( TmProd "l"
                      ( TmIndType "list"
                        [ TmRel "T" 3 ])
                      ( TmAppl
                        [ TmRel "P" 3
                        , TmRel "l" 0 ]))
                    ( TmLambda "l"
                      ( TmIndType "list"
                        [ TmRel "T" 4 ])
                      ( TmMatch 1
                        ( TmRel "l" 0 )
                          "l0"
                        [ "list"
                        , "_" ]
                        ( TmAppl
                          [ TmRel "P" 5
                          , TmRel "l0" 0 ])
                        [ Equation
                          [ "nil"
                          , "_" ]
                          ( TmRel "f" 3 )
                        , Equation
                          [ "cons"
                          , "_"
                          , "t"
                          , "l0" ]
                          ( TmAppl
                            [ TmRel "f0" 4
                            , TmRel "t" 1
                            , TmRel "l0" 0
                            , TmAppl
                              [ TmRel "F" 3
                              , TmRel "l0" 0 ]])]))))))))))
  , ( "list"
    , IndTypeBind 1
      ( TmProd "T"
          TmType
          TmType )
      ( TmLambda "T"
          TmType
        ( TmIndType "list"
          [ TmRel "T" 0 ]))
      [ Constructor "nil"
        ( TmProd "T"
            TmType
          ( TmIndType "list"
            [ TmRel "T" 0 ]))
        ( TmLambda "T"
            TmType
          ( TmConstr "nil"
            [ TmRel "T" 0 ]))
      , Constructor "cons"
        ( TmProd "T"
            TmType
          ( TmProd "_"
            ( TmRel "T" 0 )
            ( TmProd "_"
              ( TmIndType "list"
                [ TmRel "T" 1 ])
              ( TmIndType "list"
                [ TmRel "T" 2 ]))))
        ( TmLambda "T"
            TmType
          ( TmLambda "t"
            ( TmRel "T" 0 )
            ( TmLambda "l"
              ( TmIndType "list"
                [ TmRel "T" 1 ])
              ( TmConstr "cons"
                [ TmRel "T" 2
                , TmRel "t" 1
                , TmRel "l" 0 ]))))])] ++ realNatlistContext

realIlistContext :: Context
realIlistContext =
  [ ( "ilist_rect"
    , TmAbbBind
      ( TmProd "T"
          TmType
        ( TmProd "P"
          ( TmProd "n"
            ( TmIndType "nat" [])
            ( TmProd "_"
              ( TmIndType "ilist"
                [ TmRel "T" 1
                , TmRel "n" 0 ])
                TmType ))
          ( TmProd "f"
            ( TmAppl
              [ TmRel "P" 0
              , TmConstr "O" []
              , TmConstr "inil"
                [ TmRel "T" 1 ]])
            ( TmProd "f0"
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
              ( TmProd "n"
                ( TmIndType "nat" [])
                ( TmProd "i"
                  ( TmIndType "ilist"
                    [ TmRel "T" 4
                    , TmRel "n" 0 ])
                  ( TmAppl
                    [ TmRel "P" 4
                    , TmRel "n" 1
                    , TmRel "i" 0 ])))))))
      ( Just
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
                                , TmRel "i0" 0 ]])])))))))))))
  , ( "ilist"
    , IndTypeBind 1
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
      [ Constructor "inil"
        ( TmProd "T"
            TmType
          ( TmIndType "ilist"
            [ TmRel "T" 0
            , TmConstr "O" []]))
        ( TmLambda "T"
            TmType
          ( TmConstr "inil"
            [ TmRel "T" 0 ]))
      , Constructor "icons"
        ( TmProd "T"
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
                    [ TmRel "n" 2 ]])))))
        ( TmLambda "T"
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
                  , TmRel "i" 0 ])))))])] ++ realListContext

realExContext :: Context
realExContext =
  [ ( "ex_rect"
    , TmAbbBind
      ( TmProd "A"
        TmType
      ( TmProd "P"
        ( TmProd "_"
          ( TmRel "A" 0 )
            TmType )
        ( TmProd "P0"
          ( TmProd "_"
            ( TmIndType "ex"
              [ TmRel "A" 1
              , TmRel "P" 0 ])
              TmType )
          ( TmProd "f"
            ( TmProd "x"
              ( TmRel "A" 2 )
              ( TmProd "f0"
                ( TmAppl
                  [ TmRel "P" 2
                  , TmRel "x" 0 ])
                ( TmAppl
                  [ TmRel "P0" 2
                  , TmConstr "ex_intro"
                    [ TmRel "A" 4
                    , TmRel "P" 3
                    , TmRel "x" 1
                    , TmRel "f0" 0 ]])))
            ( TmProd "e"
              ( TmIndType "ex"
                [ TmRel "A" 3
                , TmRel "P" 2 ])
              ( TmAppl
                [ TmRel "P0" 2
                , TmRel "e" 0 ]))))))
      ( Just
        ( TmLambda "A"
          TmType
        ( TmLambda "P"
          ( TmProd "_"
            ( TmRel "A" 0 )
              TmType )
          ( TmLambda "P0"
            ( TmProd "_"
              ( TmIndType "ex"
                [ TmRel "A" 1
                , TmRel "P" 0 ])
                TmType )
            ( TmLambda "f"
              ( TmProd "x"
                ( TmRel "A" 2 )
                ( TmProd "f0"
                  ( TmAppl
                    [ TmRel "P" 2
                    , TmRel "x" 0 ])
                  ( TmAppl
                    [ TmRel "P0" 2
                    , TmConstr "ex_intro"
                      [ TmRel "A" 4
                      , TmRel "P" 3
                      , TmRel "x" 1
                      , TmRel "f0" 0 ]])))
              ( TmLambda "e"
                ( TmIndType "ex"
                  [ TmRel "A" 3
                  , TmRel "P" 2 ])
                ( TmMatch 2
                  ( TmRel "e" 0 )
                    "e0"
                  [ "ex"
                  , "_"
                  , "_" ]
                  ( TmAppl
                    [ TmRel "P0" 3
                    , TmRel "e0" 0 ])
                  [ Equation
                    [ "ex_intro"
                    , "_"
                    , "_"
                    , "x"
                    , "f0" ]
                    ( TmAppl
                      [ TmRel "f" 3
                      , TmRel "x" 1
                      , TmRel "f0" 0 ])]))))))))
  , ( "ex"
    , IndTypeBind 2
      ( TmProd "A"
          TmType
        ( TmProd "P"
          ( TmProd "_"
            ( TmRel "A" 0 )
              TmType )
            TmType ))
      ( TmLambda "A"
          TmType
        ( TmLambda "P"
          ( TmProd "_"
            ( TmRel "A" 0 )
              TmType )
          ( TmIndType "ex"
            [ TmRel "A" 1
            , TmRel "P" 0 ])))
      [ Constructor "ex_intro"
        ( TmProd "A"
            TmType
          ( TmProd "P"
            ( TmProd "_"
              ( TmRel "A" 0 )
                TmType )
            ( TmProd "x"
              ( TmRel "A" 1 )
              ( TmProd "_"
                ( TmAppl
                  [ TmRel "P" 1
                  , TmRel "x" 0 ])
                ( TmIndType "ex"
                  [ TmRel "A" 3
                  , TmRel "P" 2 ])))))
        ( TmLambda "A"
            TmType
          ( TmLambda "P"
            ( TmProd "_"
              ( TmRel "A" 0 )
                TmType )
            ( TmLambda "x"
              ( TmRel "A" 1 )
              ( TmLambda "f"
                ( TmAppl
                  [ TmRel "P" 1
                  , TmRel "x" 0 ])
                ( TmConstr "ex_intro"
                  [ TmRel "A" 3
                  , TmRel "P" 2
                  , TmRel "x" 1
                  , TmRel "f" 0 ])))))])] ++ realIlistContext

realEx2Context :: Context
realEx2Context =
  [ ( "ex2_rect"
    , TmAbbBind
      ( TmProd "A"
        TmType
      ( TmProd "P"
        ( TmProd "_"
          ( TmRel "A" 0 )
            TmType )
        ( TmProd "Q"
          ( TmProd "_"
            ( TmRel "A" 1 )
              TmType )
          ( TmProd "P0"
            ( TmProd "_"
              ( TmIndType "ex2"
                [ TmRel "A" 2
                , TmRel "P" 1
                , TmRel "Q" 0 ])
                TmType )
            ( TmProd "f"
              ( TmProd "x"
                ( TmRel "A" 3 )
                ( TmProd "f0"
                  ( TmAppl
                    [ TmRel "P" 3
                    , TmRel "x" 0 ])
                  ( TmProd "f1"
                    ( TmAppl
                      [ TmRel "Q" 3
                      , TmRel "x" 1 ])
                    ( TmAppl
                      [ TmRel "P0" 3
                      , TmConstr "ex_intro2"
                        [ TmRel "A" 6
                        , TmRel "P" 5
                        , TmRel "Q" 4
                        , TmRel "x" 2
                        , TmRel "f0" 1
                        , TmRel "f1" 0 ]]))))
              ( TmProd "e"
                ( TmIndType "ex2"
                  [ TmRel "A" 4
                  , TmRel "P" 3
                  , TmRel "Q" 2 ])
                ( TmAppl
                  [ TmRel "P0" 2
                  , TmRel "e" 0 ])))))))
      ( Just
        ( TmLambda "A"
          TmType
        ( TmLambda "P"
          ( TmProd "_"
            ( TmRel "A" 0 )
              TmType )
          ( TmLambda "Q"
            ( TmProd "_"
              ( TmRel "A" 1 )
                TmType )
            ( TmLambda "P0"
              ( TmProd "_"
                ( TmIndType "ex2"
                  [ TmRel "A" 2
                  , TmRel "P" 1
                  , TmRel "Q" 0 ])
                  TmType )
              ( TmLambda "f"
                ( TmProd "x"
                  ( TmRel "A" 3 )
                  ( TmProd "f0"
                    ( TmAppl
                      [ TmRel "P" 3
                      , TmRel "x" 0 ])
                    ( TmProd "f1"
                      ( TmAppl
                        [ TmRel "Q" 3
                        , TmRel "x" 1 ])
                      ( TmAppl
                        [ TmRel "P0" 3
                        , TmConstr "ex_intro2"
                          [ TmRel "A" 6
                          , TmRel "P" 5
                          , TmRel "Q" 4
                          , TmRel "x" 2
                          , TmRel "f0" 1
                          , TmRel "f1" 0 ]]))))
                ( TmLambda "e"
                  ( TmIndType "ex2"
                    [ TmRel "A" 4
                    , TmRel "P" 3
                    , TmRel "Q" 2 ])
                  ( TmMatch 3
                    ( TmRel "e" 0 )
                      "e0"
                    [ "ex2"
                    , "_"
                    , "_"
                    , "_" ]
                    ( TmAppl
                      [ TmRel "P0" 3
                      , TmRel "e0" 0 ])
                    [ Equation
                      [ "ex_intro2"
                      , "_"
                      , "_"
                      , "_"
                      , "x"
                      , "f0"
                      , "f1" ]
                      ( TmAppl
                        [ TmRel "f" 4
                        , TmRel "x" 2
                        , TmRel "f0" 1
                        , TmRel "f1" 0 ])])))))))))
  , ( "ex2"
    , IndTypeBind 3
    ( TmProd "A"
        TmType
      ( TmProd "P"
        ( TmProd "_"
          ( TmRel "A" 0 )
            TmType )
        ( TmProd "Q"
          ( TmProd "_"
            ( TmRel "A" 1 )
              TmType )
            TmType )))
    ( TmLambda "A"
        TmType
      ( TmLambda "P"
        ( TmProd "_"
          ( TmRel "A" 0 )
            TmType )
        ( TmLambda "Q"
          ( TmProd "_"
            ( TmRel "A" 1 )
              TmType )
          ( TmIndType "ex2"
            [ TmRel "A" 2
            , TmRel "P" 1
            , TmRel "Q" 0 ]))))
    [ Constructor "ex_intro2"
      ( TmProd "A"
          TmType
        ( TmProd "P"
          ( TmProd "_"
            ( TmRel "A" 0 )
              TmType )
          ( TmProd "Q"
            ( TmProd "_"
              ( TmRel "A" 1 )
                TmType )
            ( TmProd "x"
              ( TmRel "A" 2 )
              ( TmProd "_"
                ( TmAppl
                  [ TmRel "P" 2
                  , TmRel "x" 0 ])
                ( TmProd "_"
                  ( TmAppl
                    [ TmRel "Q" 2
                    , TmRel "x" 1 ])
                  ( TmIndType "ex2"
                    [ TmRel "A" 5
                    , TmRel "P" 4
                    , TmRel "Q" 3 ])))))))
      ( TmLambda "A"
          TmType
        ( TmLambda "P"
          ( TmProd "_"
            ( TmRel "A" 0 )
              TmType )
          ( TmLambda "Q"
            ( TmProd "_"
              ( TmRel "A" 1 )
                TmType )
            ( TmLambda "x"
              ( TmRel "A" 2 )
              ( TmLambda "f"
                ( TmAppl
                  [ TmRel "P" 2
                  , TmRel "x" 0 ])
                ( TmLambda "f0"
                  ( TmAppl
                    [ TmRel "Q" 2
                    , TmRel "x" 1 ])
                  ( TmConstr "ex_intro2"
                    [ TmRel "A" 5
                    , TmRel "P" 4
                    , TmRel "Q" 3
                    , TmRel "x" 2
                    , TmRel "f" 1
                    , TmRel "f0" 0 ])))))))])] ++ realExContext

realPlusContext :: Context
realPlusContext =
  ( "plus"
    , TmAbbBind
      (TmProd "a"
        ( TmIndType "nat" [])
        ( TmProd "b"
          ( TmIndType "nat" [])
          ( TmIndType "nat" [])))
      ( Just
        ( TmFix 1
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
                  ( TmConstr "S"
                    [ TmAppl
                      [ TmRel "plus" 3
                      , TmRel "n" 0
                      , TmRel "b" 1 ]])]))))))) : realEx2Context

realPlus1Context :: Context
realPlus1Context =
  ( "plus1"
  , TmAbbBind
    (TmProd "a"
        ( TmIndType "nat" [])
        ( TmProd "b"
          ( TmIndType "nat" [])
          ( TmIndType "nat" [])))
    ( Just ( TmRel "plus" 0 ))) : realPlusContext

realFEqualContext :: Context
realFEqualContext =
  ( "f_equal"
  , TmAbbBind
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
                [ TmRel "A" 4
                , TmRel "x" 1
                , TmRel "y" 0 ])
              ( TmIndType "eq"
                [ TmRel "B" 4
                , TmAppl
                  [ TmRel "f" 3
                  , TmRel "x" 2 ]
                , TmAppl
                  [ TmRel "f" 3
                  , TmRel "y" 1 ]])))))))
    ( Just
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
                  [ TmRel "A" 4
                  , TmRel "x" 1
                  , TmRel "y" 0 ])
                ( TmMatch 2
                  ( TmRel "H" 0 )
                    "H0"
                  [ "eq"
                  , "_"
                  , "_"
                  , "y0" ]
                  ( TmIndType "eq"
                    [ TmRel "B" 6
                    , TmAppl
                      [ TmRel "f" 5
                      , TmRel "x" 4 ]
                    , TmAppl
                      [ TmRel "f" 5
                      , TmRel "y0" 1 ]])
                  [ Equation
                    [ "eq_refl"
                    , "_"
                    , "_" ]
                    ( TmConstr "eq_refl"
                      [ TmRel "B" 4
                      , TmAppl
                        [ TmRel "f" 3
                        , TmRel "x" 2 ]])]))))))))) : realPlus1Context

realP1arguContext :: Context
realP1arguContext =
  [ ( "p1argu_rect"
    , TmAbbBind
      ( TmProd "a"
        ( TmIndType "nat" [])
        ( TmProd "b"
          ( TmIndType "nat" [])
          ( TmProd "P"
            ( TmProd "n"
              ( TmIndType "nat" [])
              ( TmProd "_"
                ( TmIndType "p1argu"
                  [ TmRel "a" 2
                  , TmRel "b" 1
                  , TmRel "n" 0 ])
                  TmType ))
            ( TmProd "f"
              ( TmAppl
                [ TmRel "P" 0
                , TmRel "a" 2
                , TmConstr "lp"
                  [ TmRel "a" 2
                  , TmRel "b" 1 ]])
              ( TmProd "f0"
                ( TmAppl
                  [ TmRel "P" 1
                  , TmRel "b" 2
                  , TmConstr "rp"
                    [ TmRel "a" 3
                    , TmRel "b" 2 ]])
                ( TmProd "n"
                  ( TmIndType "nat" [])
                  ( TmProd "p"
                    ( TmIndType "p1argu"
                      [ TmRel "a" 5
                      , TmRel "b" 4
                      , TmRel "n" 0 ])
                    ( TmAppl
                      [ TmRel "P" 4
                      , TmRel "n" 1
                      , TmRel "p" 0 ]))))))))
      ( Just
        ( TmLambda "a"
          ( TmIndType "nat" [])
          ( TmLambda "b"
            ( TmIndType "nat" [])
            ( TmLambda "P"
              ( TmProd "n"
                ( TmIndType "nat" [])
                ( TmProd "_"
                  ( TmIndType "p1argu"
                    [ TmRel "a" 2
                    , TmRel "b" 1
                    , TmRel "n" 0 ])
                    TmType ))
              ( TmLambda "f"
                ( TmAppl
                  [ TmRel "P" 0
                  , TmRel "a" 2
                  , TmConstr "lp"
                    [ TmRel "a" 2
                    , TmRel "b" 1 ]])
                ( TmLambda "f0"
                  ( TmAppl
                    [ TmRel "P" 1
                    , TmRel "b" 2
                    , TmConstr "rp"
                      [ TmRel "a" 3
                      , TmRel "b" 2 ]])
                  ( TmLambda "n"
                    ( TmIndType "nat" [])
                    ( TmLambda "p"
                      ( TmIndType "p1argu"
                        [ TmRel "a" 5
                        , TmRel "b" 4
                        , TmRel "n" 0 ])
                      ( TmMatch 2
                        ( TmRel "p" 0 )
                          "p0"
                        [ "p1argu"
                        , "_"
                        , "_"
                        , "n0" ]
                        ( TmAppl
                          [ TmRel "P" 6
                          , TmRel "n0" 1
                          , TmRel "p0" 0 ])
                        [ Equation
                          [ "lp"
                          , "_"
                          , "_" ]
                          ( TmRel "f" 3 )
                        , Equation
                          [ "rp"
                          , "_"
                          , "_" ]
                          ( TmRel "f0" 2 )]))))))))))
  , ( "p1argu"
    , IndTypeBind 2
    ( TmProd "a"
      ( TmIndType "nat" [])
      ( TmProd "b"
        ( TmIndType "nat" [])
        ( TmProd "_"
          ( TmIndType "nat" [])
            TmType )))
    ( TmLambda "a"
      ( TmIndType "nat" [])
      ( TmLambda "b"
        ( TmIndType "nat" [])
        ( TmLambda ".0"
          ( TmIndType "nat" [])
          ( TmIndType "p1argu"
            [ TmRel "a" 2
            , TmRel "b" 1
            , TmRel ".0" 0 ]))))
    [ Constructor"lp"
      ( TmProd "a"
        ( TmIndType "nat" [])
        ( TmProd "b"
          ( TmIndType "nat" [])
          ( TmIndType "p1argu"
            [ TmRel "a" 1
            , TmRel "b" 0
            , TmRel "a" 1 ])))
      ( TmLambda "a"
        ( TmIndType "nat" [])
        ( TmLambda "b"
          ( TmIndType "nat" [])
          ( TmConstr "lp"
            [ TmRel "a" 1
            , TmRel "b" 0 ])))
    , Constructor "rp"
      ( TmProd "a"
        ( TmIndType "nat" [])
        ( TmProd "b"
          ( TmIndType "nat" [])
          ( TmIndType "p1argu"
            [ TmRel "a" 1
            , TmRel "b" 0
            , TmRel "b" 0 ])))
      ( TmLambda "a"
        ( TmIndType "nat" [])
        ( TmLambda "b"
          ( TmIndType "nat" [])
          ( TmConstr "rp"
            [ TmRel "a" 1
            , TmRel "b" 0 ])))])] ++ realFEqualContext

realP2arguContext :: Context
realP2arguContext =
  [ ( "p2argu_rect"
    , TmAbbBind
      ( TmProd "a"
        ( TmIndType "nat" [])
        ( TmProd "P"
          ( TmProd "n"
            ( TmIndType "nat" [])
            ( TmProd "n0"
              ( TmIndType "nat" [])
              ( TmProd "_"
                ( TmIndType "p2argu"
                  [ TmRel "a" 2
                  , TmRel "n" 1
                  , TmRel "n0" 0 ])
                  TmType )))
          ( TmProd "f"
            ( TmAppl
              [ TmRel "P" 0
              , TmRel "a" 1
              , TmRel "a" 1
              , TmConstr "p2"
                [ TmRel "a" 1 ]])
            ( TmProd "n"
              ( TmIndType "nat" [])
              ( TmProd "n0"
                ( TmIndType "nat" [])
                ( TmProd "p"
                  ( TmIndType "p2argu"
                    [ TmRel "a" 4
                    , TmRel "n" 1
                    , TmRel "n0" 0 ])
                  ( TmAppl
                    [ TmRel "P" 4
                    , TmRel "n" 2
                    , TmRel "n0" 1
                    , TmRel "p" 0 ])))))))
      ( Just
        ( TmLambda "a"
          ( TmIndType "nat" [])
          ( TmLambda "P"
            ( TmProd "n"
              ( TmIndType "nat" [])
              ( TmProd "n0"
                ( TmIndType "nat" [])
                ( TmProd "_"
                  ( TmIndType "p2argu"
                    [ TmRel "a" 2
                    , TmRel "n" 1
                    , TmRel "n0" 0 ])
                    TmType )))
            ( TmLambda "f"
              ( TmAppl
                [ TmRel "P" 0
                , TmRel "a" 1
                , TmRel "a" 1
                , TmConstr "p2"
                  [ TmRel "a" 1 ]])
              ( TmLambda "n"
                ( TmIndType "nat" [])
                ( TmLambda "n0"
                  ( TmIndType "nat" [])
                  ( TmLambda "p"
                    ( TmIndType "p2argu"
                      [ TmRel "a" 4
                      , TmRel "n" 1
                      , TmRel "n0" 0 ])
                    ( TmMatch 1
                      ( TmRel "p" 0 )
                        "p0"
                      [ "p2argu"
                      , "_"
                      , "n1"
                      , "n2" ]
                      ( TmAppl
                        [ TmRel "P" 7
                        , TmRel "n1" 2
                        , TmRel "n2" 1
                        , TmRel "p0" 0 ])
                      [ Equation
                        [ "p2"
                        , "_" ]
                        ( TmRel "f" 3 )])))))))))
    , ( "p2argu"
      , IndTypeBind 1
      ( TmProd "a"
        ( TmIndType "nat" [])
        ( TmProd "_"
          ( TmIndType "nat" [])
          ( TmProd "_"
            ( TmIndType "nat" [])
              TmType )))
      ( TmLambda "a"
        ( TmIndType "nat" [])
        ( TmLambda ".0"
          ( TmIndType "nat" [])
          ( TmLambda ".1"
            ( TmIndType "nat" [])
            ( TmIndType "p2argu"
              [ TmRel "a" 2
              , TmRel ".0" 1
              , TmRel ".1" 0 ]))))
      [ Constructor "p2"
        ( TmProd "a"
          ( TmIndType "nat" [])
          ( TmIndType "p2argu"
            [ TmRel "a" 0
            , TmRel "a" 0
            , TmRel "a" 0 ]))
        ( TmLambda "a"
          ( TmIndType "nat" [])
          ( TmConstr "p2"
            [ TmRel "a" 0 ]))])] ++ realP1arguContext
