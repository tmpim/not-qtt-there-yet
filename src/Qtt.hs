{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveFunctor #-}
module Qtt where

import Control.Concurrent (MVar)

import Data.List (intercalate)
import Data.Sequence (Seq)

data Term a
  = Set Int
  | Pi { var          :: a
       , domain       :: Term a
       , range        :: Term a
       }
  | Lam a (Term a)
  | Elim  (Elim a)
  deriving (Eq, Ord)

data Elim a
  = Var a
  | Meta (Meta a)
  | App (Elim a) (Term a)
  | Cut (Term a) (Term a)
  deriving (Eq, Ord)

data Meta a
  = MV { metaId :: a, metaSlot :: MVar (Term a), metaBlockedEqns :: MVar (Seq (Equation a)) }
  deriving (Eq)

data Value var
  = VNe (Neutral var)
  | VFn var (Value var -> Value var)
  | VPi var (Value var) (Value var -> Value var)
  | VSet Int

instance Show var => Show (Value var) where
  show = show . quote

instance Eq var => Eq (Value var) where
  VNe a == VNe b = a == b
  VFn var body == VFn var' body' = body (valueVar var') == body' (valueVar var)
  VPi var domain body == VPi var' domain' body' =
       domain == domain'
    && body (valueVar var') == body' (valueVar var)
  VSet a == VSet b = a == b
  _ == _ = False

data Neutral var
  = NVar var
  | NMeta (Qtt.Meta var)
  | NApp (Neutral var) [Value var]
  deriving (Eq)

instance Show var => Show (Neutral var) where
  show = show . quoteNeutral

data Equation var =
  Equation { equationMeta :: Meta var
           , equationSpine :: [Value var]
           , equationRHS :: Value var
           }

valueVar :: var -> Value var
valueVar = VNe . NVar

quoteNeutral :: Neutral var -> Qtt.Elim var
quoteNeutral (NVar v) = Qtt.Var v
quoteNeutral (NMeta v) = Qtt.Meta v
quoteNeutral (NApp f x) = foldl Qtt.App (quoteNeutral f) (reverse (map quote x))

quote :: Value var -> Qtt.Term var
quote (VFn var b) = Qtt.Lam var (quote (b (valueVar var)))
quote (VPi var dom range) =
  Qtt.Pi var (quote dom) (quote (range (valueVar var)))
quote (VSet i) = Qtt.Set i
quote (VNe v) = Qtt.Elim (quoteNeutral v)

(@@) :: Value var -> Value var -> Value var
VNe a @@ b = VNe $
  case a of
    NApp a xs -> NApp a (b:xs)
    _ -> NApp a [b]
VFn _ k @@ b = k b
_ @@ _ = error "Type error in (@@)"

instance Show a => Show (Term a) where
  showsPrec prec ex =
    case ex of
      Lam x p ->
        showParen (prec >= 1) $
          showChar 'λ' . shows x . showString ". " . showsPrec 0 p
      Pi var d r ->
        showParen (prec >= 1) $
          showParen True
            (shows var . showString " : " . showsPrec 0 d)
          . showString " -> "
          . shows r
      Set i -> showString "Set{" . shows i . showChar '}'
      Elim e -> shows e

instance Show a => Show (Elim a) where
  showsPrec _ (Var x) = shows x
  showsPrec prec x = showParen True $ (intercalate " " (go head:map (($ "") . showsPrec (prec + 1)) tail) ++)
    where
      (head, reverse -> tail) = spine x
      spine (App f x) =
        let (h, t) = spine f
         in (h, x:t)
      spine x = (x, [])
    
      go (Var v) = show v
      go (Meta v) = show v
      go (Cut a b) = "(" ++ showsPrec 1 a "" ++ " : " ++ show b ++ ")"
      go App{} = error "App can't be head of application"

instance Show a => Show (Meta a) where
  show (MV a _ _) = '?':show a
  
instance Ord a => Ord (Meta a) where
  compare (MV a _ _) (MV b _ _) = compare a b

instance Show var => Show (Equation var) where
  show (Equation m s r) = show m ++ " " ++ show s ++ " ≡? " ++ show r