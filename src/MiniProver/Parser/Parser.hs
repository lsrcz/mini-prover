module MiniProver.Parser.Parser where

import Text.Megaparsec
import MiniProver.Core.Syntax
import MiniProver.Parser.Lexer

addBinderAbbr :: (Name -> Term -> Term -> Term) -> Term -> [(Name, Term)] -> Term
addBinderAbbr abbrty = foldr (\(name, ty) acc -> abbrty name ty acc)

ptmtype :: Parser Term
ptmtype = TmType <$ rword "Type"

pterm :: Parser Term
pterm = try parrow
    <|> ptermnarrow

pbinder :: Parser (Name, Term)
pbinder = parens $ do
  name <- ident
  _ <- colon
  ty <- pterm
  return (name, ty)

pforall :: Parser Term
pforall = do
  _ <- rword "forall"
  binders <- some pbinder
  _ <- comma
  tm <- pterm
  return $ addBinderAbbr TmProd tm binders

pfun :: Parser Term
pfun = do
  _ <- rword "fun"
  binders <- many pbinder
  _ <- darrow
  tm <- pterm
  return $ addBinderAbbr TmLambda tm binders

pfix :: Parser Term
pfix = do
  _ <- rword "fix"
  name <- ident
  binders <- some pbinder
  _ <- colon
  ty <- pterm
  _ <- coloneq
  tm <- pterm
  return $ TmFix (-1)
    (TmLambda name
      (addBinderAbbr TmProd ty binders)
      (addBinderAbbr TmLambda tm binders))

pletin :: Parser Term
pletin = do
  _ <- rword "let"
  name <- ident
  binders <- many pbinder
  _ <- colon
  ty <- pterm
  _ <- coloneq
  tm <- pterm
  _ <- rword "in"
  bdy <- pterm
  if null binders
    then
      return $ TmLetIn name ty tm bdy
    else
      return $ TmLetIn name
        (addBinderAbbr TmProd ty binders)
        (addBinderAbbr TmLambda tm binders)
        bdy

ptermnarrow :: Parser Term
ptermnarrow = try papp
          <|> ptermnapp

parrow :: Parser Term
parrow = do
  tm1 <- ptermnarrow
  _ <- arrow
  tm2 <- pterm
  return $ TmProd "_" tm1 tm2

ptermnapp :: Parser Term
ptermnapp = try ptmtype
        <|> try pforall
        <|> try pfun
        <|> try pfix
        <|> try pletin
        <|> try pmatch
        <|> try pvar
        <|> try (parens pterm)

pvar :: Parser Term
pvar = do
  name <- ident
  return $ TmVar name

papp :: Parser Term
papp = do
  first <- ptermnapp
  lst <- some ptermnapp
  return $ TmAppl $ first : lst

pmatch :: Parser Term
pmatch = do
  _ <- rword "match"
  tm <- pterm
  _ <- rword "in"
  namelst <- some ident
  _ <- rword "return"
  rty <- pterm
  _ <- rword "with"
  eqs <- many pequation
  _ <- rword "end"
  return $ TmMatch tm namelst rty eqs

pequation :: Parser Equation
pequation = do
  _ <- mid
  namelst <- some ident
  _ <- darrow
  tm <- pterm
  return $ Equation namelst tm

paxiom :: Parser Command
paxiom = do
  _ <- rword "Axiom"
  name <- ident
  _ <- colon
  ty <- pterm
  _ <- dot
  return $ Ax name ty

pdefinition :: Parser Command
pdefinition = do
  _ <- rword "Definition"
  name <- ident
  binders <- many pbinder
  _ <- colon
  ty <- pterm
  _ <- coloneq
  tm <- pterm
  _ <- dot
  if null binders
    then
      return $ Def name ty tm
    else
      return $ Def name
        (addBinderAbbr TmProd ty binders)
        (addBinderAbbr TmLambda tm binders)

pinductive :: Parser Command
pinductive = do
  _ <- rword "Inductive"
  name <- ident
  binders <- many pbinder
  _ <- colon
  arity <- pterm
  _ <- coloneq
  constrlst <- many pconstr
  _ <- dot
  let ty = addBinderAbbr TmProd arity binders
  return $ Ind name (length binders)
    ty
    (modifyLast [] (TmIndType name) $ giveNameToAbs 0 $ prodToLambda ty)
    (map 
      (\(namec,tyc) ->
        let 
          tyc1 = addBinderAbbr TmProd tyc binders
        in
          ( namec
          , typesToIndType name tyc1
          , typesToIndType name $ modifyLast [] (TmConstr namec) $ 
              giveNameToAbs 0 $ prodToLambda tyc1))
      constrlst)

giveNameToAbs :: Int -> Term -> Term
giveNameToAbs i (TmProd name ty tm)
  | name == "_" = TmProd ('.' : show i) ty $ giveNameToAbs (i + 1) tm
  | otherwise  = TmProd name ty $ giveNameToAbs i tm
giveNameToAbs i (TmLambda name ty tm)
  | name == "_" = TmLambda ('.' : show i) ty $ giveNameToAbs (i + 1) tm
  | otherwise  = TmLambda name ty $ giveNameToAbs i tm
giveNameToAbs _ a = a

modifyLast :: [Term] -> ([Term] -> Term) -> Term -> Term
modifyLast ls f (TmProd name ty tm) = TmProd name ty $ modifyLast (TmVar name : ls) f tm
modifyLast ls f (TmLambda name ty tm) = TmLambda name ty $ modifyLast (TmVar name : ls) f tm
modifyLast ls f _ = f $ reverse ls

prodToLambda :: Term -> Term
prodToLambda (TmProd name ty tm) = TmLambda name ty $ prodToLambda tm
prodToLambda tm = tm

singleTypeToIndType :: Name -> Term -> Term
singleTypeToIndType namet tm@(TmVar name)
  | namet == name = TmIndType name []
  | otherwise = tm
singleTypeToIndType namet tm@(TmAppl (TmVar name : ls))
  | namet == name = TmIndType name ls
  | otherwise = tm
singleTypeToIndType _ tm = tm

typesToIndType :: Name -> Term -> Term
typesToIndType namet (TmProd name ty tm) =
  TmProd name (singleTypeToIndType namet ty) $ typesToIndType namet tm
typesToIndType namet (TmLambda name ty tm) =
  TmLambda name (singleTypeToIndType namet ty) $ typesToIndType namet tm
typesToIndType namet tm = singleTypeToIndType namet tm

pconstr :: Parser (Name, Term)
pconstr = do
  _ <- mid
  name <- ident
  _ <- colon
  ty <- pterm
  return (name, ty)

pfixdefinition :: Parser Command
pfixdefinition = do
  _ <- rword "Fixpoint"
  name <- ident
  binders <- some pbinder
  _ <- colon
  ty <- pterm
  _ <- coloneq
  tm <- pterm
  _ <- dot
  return $ Fix name
    ( TmFix (-1)
      (TmLambda name
        (addBinderAbbr TmProd ty binders)
        (addBinderAbbr TmLambda tm binders)))

pcommand :: Parser Command
pcommand = try paxiom
       <|> try pdefinition
       <|> try pinductive
       <|> try pfixdefinition
