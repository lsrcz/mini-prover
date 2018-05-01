module MiniProver.Core.Syntax (
    Sort(..)
  , Name
  , Term(..)
  , Obj(..)
  , Constructor(..)
  , Equation(..)
  , Ref(..)
  ) where

data Sort = Prop | Type | Set deriving (Eq, Show)

type Name = String

data Term =
    TmRel Int                       -- DeBruijn index, 1 based
  | TmVar Name
  | TmAppl [Term]                   -- arguments
  | TmProd Name Term Term           -- binder source target
  | TmLambda Name Term Term         -- binder source target
  | TmLetIn Name Term Term Term     -- binder type term body
  | TmConst Ref                     -- Ref : Indtype | constr
  | TmSort Sort                     -- sort
  | TmMatch Term [Equation]         -- ind. Term [Equation]
  deriving (Eq, Show)

data Obj =
    Constant Name (Maybe Term) Term -- name definition type
  | Fixpoint Name Term              -- name function body
  | Inductive Name Term [Constructor] -- Typename Arity (Constructor list)
  deriving (Eq, Show)

data Constructor = Constructor Name Term deriving (Eq, Show)

data Equation = Equation [Name] Term deriving (Eq, Show)


-- dummy
data Ref = Ref Int deriving (Eq, Show)