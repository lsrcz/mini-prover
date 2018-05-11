module MiniProver.Core.Syntax (
    Name
  , Index
  , Term(..)
  , Command(..)
  , Binding(..)
  , Constructor(..)
  , Equation(..)
  ) where

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
  | TmIndTypeRef Name
  | TmConstrRef Name
  | TmIndType Name [Term]           -- should only be full, refering to the type
  | TmConstr Name [Term]            -- should only be full, refering to the term
  | TmType                          -- sort
  | TmMatch Term [Name] Term [Equation]  -- ind. Term [Names] RetType [Equation]
  | DummyTm                         -- Just for testing
  deriving (Eq, Show)

data Command =
    Ax Name Term                     -- name type
  | Def Name Term Term               -- name type term
  | Ind Name Int Term Term [(Name, Term, Term)] -- name int ty tm [(name, ty, tm)]
  | Fix Name Term
  | Theorem Name Term
  | Proof
  | Qed
  | Print Name
  | Check Term
  | DummyCmd                         -- Just for testing
  deriving (Eq, Show)

data Binding =
    NameBind
  | IndTypeBind Int Term Term [Constructor]    -- numOfArguments type term
  | VarBind Term                               -- only for typing
  | TmAbbBind Term (Maybe Term)                -- type term
  deriving (Eq, Show)

data Constructor = Constructor Name Term Term deriving (Eq, Show)  -- type term

data Equation = Equation [Name] Term deriving (Eq, Show)

