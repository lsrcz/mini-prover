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