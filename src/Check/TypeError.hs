module Check.TypeError where

import Qtt (Term, Elim, quote, Meta, Value)

import Presyntax (Expr)
import Data.List (intercalate)

data TypeError a
  = NotInScope a
  | NotEqual (Value a) (Value a)
  | NotPi (Value a)
  | NotSet (Value a)
  | CanNotInfer (Expr a)
  | NotMillerPattern (Meta a) [Value a] (Value a)
  | Timing (TypeError a) (Timing a)
  | InvalidDataKind (Value a)
  | WrongDataReturn (Elim a) (Term a)
  deriving (Eq)

data Timing a
  = WhenSolving (Meta a) [Value a] (Value a)
  deriving (Eq)

instance Show a => Show (TypeError a) where
  show (NotInScope a) = "Variable not in scope: " ++ show a
  show (NotPi v) = "Type is not a product type: " ++ show (quote v)
  show (NotSet v) = "Type is not a universe type: " ++ show (quote v)
  show (NotEqual a b) = "Types " ++ show (quote a) ++ " and " ++ show (quote b) ++ " are not equal."
  show (CanNotInfer e) = "Can not infer kind for type " ++ show e
  show (NotMillerPattern mv spine val) =
       "Equation "
    ++ show mv ++ " " ++ intercalate " " (map (show . quote) spine) ++ " ≡ " ++ show (quote val)
    ++ " is not in Miller pattern form"
  show (Timing e ti) =
    unlines [show e, show ti]

instance Show a => Show (Timing a) where
  show (WhenSolving mv spine val) =
    "When solving the equation " ++ show mv ++ " " ++ intercalate " " (map (show . quote) spine) ++ " ≡ " ++ show (quote val)