module MiniProver.Parser.Parser where

import Text.Megaparsec
import MiniProver.Core.Syntax
import MiniProver.Parser.Lexer

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
  return $ foldr (\(name, ty) acc -> TmProd name ty acc) tm binders

pfun :: Parser Term
pfun = do
  _ <- rword "fun"
  binders <- many pbinder
  _ <- darrow
  tm <- pterm
  return $ foldr (\(name,ty) acc -> TmLambda name ty acc) tm binders

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
        (foldr (\(namei,tyi) acc -> TmProd namei tyi acc) ty binders)
        (foldr (\(namei,tyi) acc -> TmLambda namei tyi acc) tm binders)
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