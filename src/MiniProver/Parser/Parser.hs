module MiniProver.Parser.Parser where

import Text.Megaparsec
import MiniProver.Core.Syntax
import MiniProver.Parser.Lexer

addBinderAbbr :: (Name -> Term -> Term -> Term) -> Term -> [(Name, Term)] -> Term
addBinderAbbr abbrty = foldr (\(name, ty) acc -> abbrty name ty acc)

psort :: Parser Sort
psort = (Prop <$ rword "Prop")
    <|> (Set <$ rword "Set")
    <|> (Type <$ rword "Type")

ptmsort :: Parser Term
ptmsort = do
  sort <- psort
  return $ TmSort sort

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
  return $ TmFix
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
ptermnapp = try ptmsort
        <|> try pforall
        <|> try pfun
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
  _ <- rword "with"
  eqs <- many pequation
  _ <- rword "end"
  return $ TmMatch tm eqs

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
  return $ Ind name (length binders)
    (addBinderAbbr TmProd arity binders)
    (map 
      (\(namec,tyc) ->
        (namec,
          addBinderAbbr TmProd tyc binders))
      constrlst)

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
    (TmLambda name
      (addBinderAbbr TmProd ty binders)
      (addBinderAbbr TmLambda tm binders))