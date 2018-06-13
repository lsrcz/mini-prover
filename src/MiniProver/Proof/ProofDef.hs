module MiniProver.Proof.ProofDef where

import MiniProver.Core.Syntax
import MiniProver.Core.Context
import MiniProver.Core.Typing
import System.IO.Unsafe
import MiniProver.PrettyPrint.Colorful
import MiniProver.PrettyPrint.PrettyPrint
import MiniProver.PrettyPrint.PrettyPrintAST

data ProofCommand =
    Proof
  | Undo
  | Restart
  | Admitted
  | Abort
  | Qed
  deriving (Show, Eq)

data Tactic =
    Exact Term
  | Apply Term (Maybe Name)
  | Intro [Name]
  | Intros
  | Destruct Term
  | Induction Term
  | Rewrite Bool Term (Maybe Name)
  | Simpl (Maybe Name)
  | Reflexivity
  | Symmetry
  | Unfold Name (Maybe Name)
  | Inversion Name
  | Split
  | LeftTac
  | RightTac
  | Exists Term
  | Equvalence Name
  | Equivalence Name
  deriving (Show, Eq)

data ProofInput =
    PCmd ProofCommand
  | PTac Tactic
  deriving (Show, Eq)

newtype TacticError = TacticError String deriving (Show, Eq)

data Goal = Goal Int Context Term deriving (Show, Eq)

type ResultFunc = [Term] -> Term
data Result = Result [Goal] ResultFunc

getGoalList :: Result -> [Goal]
getGoalList (Result goallst _) = goallst

getResultFunc :: Result -> ResultFunc
getResultFunc (Result _ rf) = rf

checkResult :: Goal -> Tactic -> Term -> Term
checkResult g@(Goal i ctx ty) tactic tm = 
  if typeeq ctx (typeof ctx tm) (Right ty) then tm else seq 
    (unsafePerformIO $ do
      putStrLn $ frontGroundColor BRED "FATAL Error"
      putStrLn $ frontGroundColor BYELLOW "When trying to handle tactic:"
      print tactic
      putStrLn $ frontGroundColor BYELLOW "The goal is"
      prettyPrint ty
      putStrLn $ frontGroundColor BYELLOW "with AST"
      prettyPrintAST ty
      putStrLn $ frontGroundColor BYELLOW "The term constructed is"
      prettyPrint tm
      putStrLn $ frontGroundColor BYELLOW "with AST"
      prettyPrintAST tm
      putStrLn $ frontGroundColor BYELLOW "in local context"
      print (take i ctx)
      case typeof ctx tm of
        Left (TypingError tm str) -> do
          putStrLn $ frontGroundColor BRED "Typing error in the term: "
          prettyPrint tm
          putStrLn str
        Right ty -> do
          putStrLn $ frontGroundColor BYELLOW "The type of the constructed term is"
          prettyPrint ty
    )
    error $ frontGroundColor BRED "Tactic typing error, this should not happen"

instance Show Result where
  show (Result goallst f) = "Goals\n" ++ unlines (map show goallst) ++ "\nfunc\n" ++ show (f [TmVar ("Goal" ++ show i) | i <- [1..]])
