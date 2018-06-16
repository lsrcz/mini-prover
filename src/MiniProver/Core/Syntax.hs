module MiniProver.Core.Syntax (
    Name
  , Index
  , Term(..)
  , termEqNameless
  , Command(..)
  , Binding(..)
  , Constructor(..)
  , Equation(..)
  ) where

type Name = String
type Index = Int

data Term =
    TmRel Name Index                     -- DeBruijn index, 0 based
  | TmVar Name
  | TmAppl [Term]                   -- arguments
  | TmProd Name Term Term           -- binder source target
  | TmLambda Name Term Term         -- binder source target
  | TmFix Int Term
  | TmLetIn Name Term Term Term     -- binder type term body
  | TmIndType Name [Term]           -- should only be full, refering to the type
  | TmConstr Name [Term]            -- should only be full, refering to the term
  | TmType                          -- sort
  | TmTypeHigher
  | TmMatch Int Term Name [Name] Term [Equation]
  | DummyTm                         -- Just for testing
  deriving (Eq, Show)

-- only bulit term, if TmVar, compare there names
termEqNameless :: Term -> Term -> Bool
termEqNameless (TmRel _ idx1) (TmRel _ idx2) = idx1 == idx2
termEqNameless (TmVar name1) (TmVar name2) = name1 == name2
termEqNameless (TmAppl termlst1) (TmAppl termlst2) =
  length termlst1 == length termlst2 &&
  and (zipWith termEqNameless termlst1 termlst2)
termEqNameless (TmProd _ ty1 tm1) (TmProd _ ty2 tm2) =
  termEqNameless ty1 ty2 && termEqNameless tm1 tm2
termEqNameless (TmLambda _ ty1 tm1) (TmLambda _ ty2 tm2) =
  termEqNameless ty1 ty2 && termEqNameless tm1 tm2
termEqNameless (TmFix _ tm1) (TmFix _ tm2) = termEqNameless tm1 tm2
termEqNameless (TmLetIn _ ty1 tm1 bdy1) (TmLetIn _ ty2 tm2 bdy2) =
  termEqNameless ty1 ty2 && termEqNameless tm1 tm2 && termEqNameless bdy1 bdy2
termEqNameless (TmIndType name1 termlst1) (TmIndType name2 termlst2) =
  name1 == name2 && length termlst1 == length termlst2 &&
  and (zipWith termEqNameless termlst1 termlst2)
termEqNameless (TmConstr name1 termlst1) (TmConstr name2 termlst2) =
  name1 == name2 && length termlst1 == length termlst2 &&
  and (zipWith termEqNameless termlst1 termlst2)
termEqNameless TmType TmType = True
termEqNameless TmTypeHigher TmTypeHigher = True
termEqNameless (TmMatch _ tm1 _ namelst1 retty1 equlst1) (TmMatch _ tm2 _ namelst2 retty2 equlst2) =
  termEqNameless tm1 tm2 && not (null namelst1) && length namelst1 == length namelst2 &&
  head namelst1 == head namelst2 && termEqNameless retty1 retty2 &&
  length equlst1 == length equlst2 && and (zipWith equEqNameless equlst1 equlst2)
termEqNameless _ _ = False

equEqNameless :: Equation -> Equation -> Bool
equEqNameless (Equation namelst1 tm1) (Equation namelst2 tm2) =
  not (null namelst1) && length namelst1 == length namelst2 && head namelst1 == head namelst2 &&
  termEqNameless tm1 tm2

data Command =
    Ax Name Term                     -- name type
  | Def Name Term Term               -- name type term
  | Ind Name Int Term Term [(Name, Term, Term)] -- name int ty tm [(name, ty, tm)]
  | Fix Name Term
  | Theorem Name Term
  | Print Name
  | Check Term
  | PrintAST Name
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

