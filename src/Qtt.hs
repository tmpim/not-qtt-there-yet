{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveFunctor #-}
module Qtt where

import Control.Concurrent (MVar)

import Data.Sequence (Seq)
import Data.Char (ord, chr)
import Data.Range
import qualified Data.Sequence as Seq

data Visibility = Visible | Invisible
  deriving (Eq, Show, Ord)

data Term a
  = Set Int
  | Pi { var          :: a
       , visbility    :: Visibility
       , domain       :: Term a
       , range        :: Term a
       }
  | Lam a (Term a)
  | Elim  (Elim a)
  deriving (Eq, Ord)

quantify :: [(var, Visibility, Term var)] -> Term var -> Term var
quantify [] t          = t
quantify ((v, vis, t):qs) r = Pi v vis t (quantify qs r)

data Elim a
  = Var a
  | Meta (Meta a)
  | App (Elim a) (Term a)
  | Cut (Term a) (Term a)
  deriving (Eq, Ord)

data Meta a
  = MV { metaId :: a
       , metaSlot :: MVar (Term a)
       , metaBlockedEqns :: MVar (Seq (Constraint a))
       , metaLocation :: Range
       , metaExpected :: Value a
       }
  deriving (Eq)

data Value var
  = VNe (Neutral var)
  | VFn var (Value var -> Value var)
  | VPi var Visibility (Value var) (Value var -> Value var)
  | VSet Int

instance (Eq var, Show var) => Show (Value var) where
  show = show . quote

instance Eq var => Eq (Value var) where
  VNe a == VNe b = a == b
  VFn var body == VFn var' body' = body (valueVar var') == body' (valueVar var)
  VPi var vis domain body == VPi var' vis' domain' body' =
       domain == domain'
    && vis == vis'
    && body (valueVar var') == body' (valueVar var)
  VSet a == VSet b = a == b
  _ == _ = False

data Neutral var
  = NVar var
  | NMeta (Qtt.Meta var)
  | NApp (Neutral var) (Seq (Value var))
  deriving (Eq)

instance (Show var, Eq var) => Show (Neutral var) where
  show = show . quoteNeutral

data Constraint var
  = Equation { equationMeta  :: Meta var
             , equationSpine :: Seq (Value var)
             , equationRHS   :: Value var
             }

valueVar :: var -> Value var
valueVar = VNe . NVar

quoteNeutral :: Neutral var -> Qtt.Elim var
quoteNeutral (NVar v) = Qtt.Var v
quoteNeutral (NMeta v) = Qtt.Meta v
quoteNeutral (NApp f x) = foldl Qtt.App (quoteNeutral f) (fmap quote x)

quote :: Value var -> Qtt.Term var
quote (VFn var b) = Qtt.Lam var (quote (b (valueVar var)))
quote (VPi var vis dom range) =
  Qtt.Pi var vis (quote dom) (quote (range (valueVar var)))
quote (VSet i) = Qtt.Set i
quote (VNe v) = Qtt.Elim (quoteNeutral v)

(@@) :: (Eq var, Show var) => Value var -> Value var -> Value var
VNe a @@ b = VNe $
  case a of
    NApp a xs -> NApp a (xs Seq.:|> b)
    _ -> NApp a (Seq.singleton b)
VFn _ k @@ b = k b
a @@ b = error $ "Type error in (@@): tried to apply " ++ show a ++ " to " ++ show b

isVarAlive :: Eq var => var -> Term var -> Bool
isVarAlive var (Elim c) = go c where
  go (Var var') = var == var'
  go (App e c) = go e || isVarAlive var c
  go Meta{} = False
  go (Cut a b) = isVarAlive var a || isVarAlive var b
isVarAlive _ Set{} = False
isVarAlive var (Lam v b) = v /= var && isVarAlive var b
isVarAlive var (Pi v _ d r) = isVarAlive var d || (v /= var && isVarAlive var r)

instance (Eq a, Show a) => Show (Term a) where
  showsPrec prec ex =
    case ex of
      Lam x p ->
        showParen (prec >= 1) $
          showChar 'λ' . shows x . showString ". " . showsPrec 0 p
      Pi var vis d r
        | isVarAlive var r ->
          showParen (prec >= 1) $
            showBracket vis
              (shows var . showString " : " . showsPrec 0 d)
            . showString " -> "
            . shows r
        | otherwise -> showsPrec 1 d . showString " -> " . showsPrec prec r
      Set i -> showString "Type" . showString (map subscript (show i))
      Elim e -> showsPrec prec e
    where subscript c = chr (ord '₀' + (ord c - ord '0'))
          showBracket Visible k = showParen True k
          showBracket Invisible k = showChar '{' . k . showChar '}'

instance (Eq a, Show a) => Show (Elim a) where
  showsPrec _ (Var x) = shows x
  showsPrec _ (Meta v) = shows v
  showsPrec _ (Cut a b) = showChar '(' . showsPrec 1 a . showString " : " . shows b . showChar ')'
  showsPrec prec x =
      showParen (prec >= 2) $
        shows head
        . foldr (\x k -> showChar ' ' . showsPrec 2 x . k) id tail
    where
      (head, reverse -> tail) = spine x
      spine (App f x) =
        let (h, t) = spine f
         in (h, x:t)
      spine x = (x, [])

instance Show a => Show (Meta a) where
  show  = ('?':) . show . metaId
  
instance Ord a => Ord (Meta a) where
  compare mv mv' = compare (metaId mv) (metaId mv')

instance (Show var, Eq var) => Show (Constraint var) where
  show (Equation m s r) = show m ++ " " ++ show s ++ " ≡? " ++ show r