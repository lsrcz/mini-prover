module MiniProver.Parser.Lexer (
    Parser
  , symbol
  , parens
  , colon
  , coloneq
  , arrow
  , larrow
  , darrow
  , dot
  , comma
  , underscore
  , mid
  , rword
  , ident
  ) where

import Data.Void
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

type Parser = Parsec Void String

sc :: Parser ()
sc = L.space space1 lineCmnt blockCmnt
  where
    lineCmnt  = L.skipLineComment "--"
    blockCmnt = L.skipBlockComment "{-" "-}"

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: String -> Parser String
symbol = L.symbol sc

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

colon :: Parser String
colon = symbol ":"

coloneq :: Parser String
coloneq = symbol ":="

arrow :: Parser String
arrow = symbol "->"

larrow :: Parser String
larrow = symbol "<-"

darrow :: Parser String
darrow = symbol "=>"

dot :: Parser String
dot = symbol "."

comma :: Parser String
comma = symbol ","

underscore :: Parser String
underscore = symbol "_"

mid :: Parser String
mid = symbol "|"

rword :: String -> Parser ()
rword w = (lexeme . try) (string w *> notFollowedBy alphaNumChar)

rws :: [String]
rws = [
    "forall", "fun", "fix", "let", "in", "match", "return", "with", "end", "Prop"
  , "Set", "Type", "Axiom", "Definition", "Inductive", "Fixpoint", "Theorem"
  , "Proof", "Qed", "exact", "apply", "intro", "intros", "destruct", "induction"
  , "rewrite", "simpl", "reflexivity", "symmetry", "Print", "Check", "Undo"
  , "Restart", "Admitted", "Abort"
  ]

ident :: Parser String
ident = (lexeme . try) (p >>= check)
  where
    p       = (:) <$> letterChar <*> many alphaNumChar
    check x = if x `elem` rws
                then fail $ "keyword " ++ show x ++ " cannot be an identifier"
                else return x