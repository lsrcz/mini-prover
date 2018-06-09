module MiniProver.Parser.Parser where

import Text.Megaparsec
import MiniProver.Core.Syntax
import MiniProver.Parser.Lexer
import MiniProver.Proof.ProofDef

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
  _ <- rword "as"
  name <- ident
  _ <- rword "in"
  namelst <- some (ident <|> underscore)
  _ <- rword "return"
  rty <- pterm
  _ <- rword "with"
  eqs <- many pequation
  _ <- rword "end"
  return $ TmMatch (-1) tm name namelst rty eqs

pequation :: Parser Equation
pequation = do
  _ <- mid
  namelst <- some (ident <|> underscore)
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

typesToIndType :: Name -> Term -> Term
typesToIndType namet (TmProd name ty tm) =
  TmProd name (typesToIndType namet ty) $ typesToIndType namet tm
typesToIndType namet (TmLambda name ty tm) =
  TmLambda name (typesToIndType namet ty) $ typesToIndType namet tm
typesToIndType namet (TmIndType name tmlst) =
  TmIndType name (map (typesToIndType namet) tmlst)
typesToIndType namet (TmConstr name tmlst) =
  TmConstr name (map (typesToIndType namet) tmlst)
typesToIndType namet tm@(TmVar name)
  | namet == name = TmIndType name []
  | otherwise = tm
typesToIndType namet (TmAppl tmlst) =
  case tmlst of
    TmVar name : ls
      | namet == name -> typesToIndType namet $ TmIndType name ls
    _ -> TmAppl (map (typesToIndType namet) tmlst)
typesToIndType namet (TmFix i tm) =
  TmFix i (typesToIndType namet tm)
typesToIndType namet (TmLetIn name ty tm bdy) =
  TmLetIn name
    (typesToIndType namet ty)
    (typesToIndType namet tm)
    (typesToIndType namet bdy)
typesToIndType namet (TmMatch i tm name namelst retty eqnlst) =
  TmMatch i (typesToIndType namet tm) name namelst
    (typesToIndType namet retty) (map (typeToIndTypeEqnlst namet) eqnlst)
typesToIndType _ tm = tm

typeToIndTypeEqnlst :: String -> Equation -> Equation
typeToIndTypeEqnlst namet (Equation namelst tm) =
  Equation namelst $ typesToIndType namet tm

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
  
ptheorem :: Parser Command
ptheorem = do
  _ <- rword "Theorem"
  name <- ident
  binders <- many pbinder
  _ <- colon
  ty <- pterm
  _ <- dot
  return $ Theorem name (addBinderAbbr TmProd ty binders)

pprint :: Parser Command
pprint = do
  _ <- rword "Print"
  name <- ident
  return $ Print name

pcheck :: Parser Command
pcheck = do
  _ <- rword "Check"
  tm <- pterm
  return $ Check tm

pcommand :: Parser Command
pcommand = try paxiom
       <|> try pdefinition
       <|> try pinductive
       <|> try pfixdefinition
       <|> try ptheorem
       <|> try pprint
       <|> try pcheck

pproofcmd :: Parser ProofCommand
pproofcmd = do
  pc <- pproofcmd'
  _ <- dot
  return pc

pproofcmd' :: Parser ProofCommand
pproofcmd' = try (Proof <$ rword "Proof")
  <|> try (Undo <$ rword "Undo")
  <|> try (Restart <$ rword "Restart")
  <|> try (Admitted <$ rword "Admitted")
  <|> try (Abort <$ rword "Abort")
  <|> try (Qed <$ rword "Qed")

ptactic :: Parser Tactic
ptactic = do
  tactic <- ptactic'
  _ <- dot
  return tactic

ptactic' :: Parser Tactic
ptactic' = try pexact
  <|> try papply
  <|> try pintro
  <|> try (Intros <$ rword "intros")
  <|> try pdestruct
  <|> try pinduction
  <|> try prewrite
  <|> try psimpl
  <|> try (Reflexivity <$ rword "reflexivity")
  <|> try (Symmetry <$ rword "symmetry")
  <|> try punfold
  <|> try pinversion

pexact :: Parser Tactic
pexact = do
  _ <- rword "exact"
  tm <- pterm
  return $ Exact tm

papply :: Parser Tactic
papply = do
  _ <- rword "apply"
  tm <- pterm
  mbid <- pmaybeinident
  return $ Apply tm mbid

pmaybeinident :: Parser (Maybe Name)
pmaybeinident = return <$> try pinidentok
  <|> return Nothing

pinidentok :: Parser Name
pinidentok = do
  _ <- rword "in"
  ident

pintro :: Parser Tactic
pintro = do
  _ <- rword "intro"
  lst <- some ident
  return $ Intro lst

pdestruct :: Parser Tactic
pdestruct = do
  _ <- rword "destruct"
  tm <- pterm
  return $ Destruct tm

pinduction :: Parser Tactic
pinduction = do
  _ <- rword "induction"
  tm <- pterm
  return $ Induction tm

prewrite :: Parser Tactic
prewrite = do
  _ <- rword "rewrite"
  isleftdir <- True <$ larrow <|> False <$ arrow <|> return False
  tm <- pterm
  mbtm <- pmaybeinterm
  return $ Rewrite isleftdir tm mbtm

pmaybeinterm :: Parser (Maybe Term)
pmaybeinterm = return <$> try pintermok
  <|> return Nothing

pintermok :: Parser Term
pintermok = do
  _ <- rword "in"
  pterm

psimpl :: Parser Tactic
psimpl = do
  _ <- rword "simpl"
  mbid <- pmaybeinident
  return $ Simpl mbid

punfold :: Parser Tactic
punfold = do
  _ <- rword "unfold"
  nm <- ident
  mbid <- pmaybeinident
  return $ Unfold nm mbid

pinversion :: Parser Tactic
pinversion = do
  _ <- rword "inversion"
  nm <- ident
  return $ Inversion nm

pproofinput :: Parser ProofInput
pproofinput = (PCmd <$> try pproofcmd) <|> (PTac <$> try ptactic)
