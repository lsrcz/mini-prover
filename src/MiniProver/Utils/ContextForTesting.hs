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
        ( TmFix
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
                ( TmMatch
                  ( TmRel "a" 1 )
                  [ "nat" ]
                  ( TmIndType "nat" [] )
                  [ Equation
                    [ "O" ]
                    ( TmRel "b" 0 )
                  , Equation
                    [ "S", "n" ]
                    ( TmAppl
                      [ TmRel "plus" 3
                      , TmRel "n" 0
                      , TmAppl
                        [ TmLambda ".0"
                          ( TmIndType "nat" [] )
                          ( TmConstr "S" [ TmRel ".0" 0 ])
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
  [ ( "zero"
    , TmAbbBind
      ( TmIndType "nat" [] )
      ( Just
        ( TmConstr "O" [] )))
  , ( "one"
    , TmAbbBind
      ( TmIndType "nat" [] )
      ( Just
        ( TmConstr "S"
          [ TmRel "zero" 0 ])))
  , ( "two"
    , TmAbbBind
      ( TmIndType "nat" [] )
      ( Just
        ( TmConstr "S"
          [ TmRel "one" 0 ])))] ++ natContext

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