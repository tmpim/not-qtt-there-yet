module Check.TypeError where

import Qtt (Visibility(..), Term, Elim, quote, Meta, Value)

import Presyntax (ExprL)
import Data.List (intercalate)

data TypeError a
  = NotInScope a
  | NotEqual (Value a) (Value a)
  | NotPi Visibility (Value a)
  | NotSet (Value a)
  | CanNotInfer (ExprL a)
  | NotMillerPattern (Meta a) [Value a] (Value a)
  | Timing (TypeError a) (Timing a)
  | InvalidDataKind (Value a)
  | WrongDataReturn (Elim a) (Term a)
  | TypeTooBig Int Int
  | Undefined a
  | NonWellFounded a Int (Value a)
  deriving (Eq)

data Timing a
  = WhenSolving (Meta a) [Value a] (Value a)
  deriving (Eq)

instance (Show a, Eq a) => Show (TypeError a) where
  show (NotInScope a) = "Variable not in scope: " ++ show a
  show (NotPi Invisible v) = "Type is not a function type: " ++ show (quote v)
  show (NotPi Visible v) = "Type is not an invisible function type: " ++ show (quote v)
  show (NotSet v) = "Type is not a universe type: " ++ show (quote v)
  show (NotEqual a b) = "Types " ++ show (quote a) ++ " and " ++ show (quote b) ++ " are not equal."
  show (CanNotInfer e) = "Can not infer kind for type " ++ show e
  show (NotMillerPattern mv spine val) =
       "Equation "
    ++ show mv ++ " " ++ intercalate " " (map (show . quote) spine) ++ " ≡ " ++ show (quote val)
    ++ " is not in Miller pattern form"
  show (TypeTooBig i j) = "Type with universe " ++ show i ++ " is too big to fit in universe Type " ++ show j
  show (Undefined a) = "The name " ++ show a ++ " was declared, but no definition was given"
  show (InvalidDataKind k) = "The kind " ++ show k ++ " is not valid as the return kind of a data declaration"
  show (WrongDataReturn ka kb) = "Expected " ++ show ka ++ " in return kind of constructor, but have " ++ show kb
  show (NonWellFounded con i arg) =
    "The type for the constructor " ++ show con ++ " is not well founded, because\n"
      ++ "  the " ++ nth i ++ " constructor argument has type " ++ show arg
  show (Timing e ti) =
    unlines [show e, show ti]

nth :: Show a => a -> [Char]
nth l =
  let c = show l
   in case last c of
        '1' -> c ++ "st"
        '2' -> c ++ "nd"
        '3' -> c ++ "rd"
        _ -> c ++ "th"

instance (Show a, Eq a) => Show (Timing a) where
  show (WhenSolving mv spine val) =
    "When solving the equation " ++ show mv ++ " " ++ intercalate " " (map (show . quote) spine) ++ " ≡ " ++ show (quote val)