module MiniProver.Core.Syntax (
    Sort(..)
  , Name
  , Index
  , Term(..)
  , Command(..)
  , Binding(..)
  , Constructor(..)
  , Equation(..)
  ) where

data Sort = Prop | Type | Set deriving (Eq, Show)

type Name = String
type Index = Int

data Term =
    TmRel Name Index                     -- DeBruijn index, 1 based
  | TmVar Name
  | TmAppl [Term]                   -- arguments
  | TmProd Name Term Term           -- binder source target
  | TmLambda Name Term Term         -- binder source target
  | TmFix Term
  | TmLetIn Name Term Term Term     -- binder type term body
  | TmIndType Name [Term]
  | TmConstr Name [Term]
  | TmSort Sort                     -- sort
  | TmMatch Term [Equation]         -- ind. Term [Equation]
  | DummyTm                         -- Just for testing
  deriving (Eq, Show)

data Command =
    Ax Name Term
  | Def Name Term Term
  | Ind Name Int Term [(Name, Term)]
  | Fix Name Term
  | Theorem Name Term
  | Proof
  | Qed
  | Print Term
  | Check Term
  | DummyCmd                         -- Just for testing
  deriving (Eq, Show)

data Binding =
    NameBind
  | IndTypeBind Int
  | ConstrBind
  | VarBind Term                          -- only for typing
  | TmAbbBind Term (Maybe Term)           -- type term
  deriving (Eq, Show)

data Constructor = Constructor Name Term deriving (Eq, Show)

data Equation = Equation [Name] Term deriving (Eq, Show)

