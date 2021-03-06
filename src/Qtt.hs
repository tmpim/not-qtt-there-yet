{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE BangPatterns #-}
module Qtt where

import Control.Concurrent (MVar)
import Control.Comonad

import qualified Data.HashSet as HashSet
import qualified Data.Sequence as Seq
import Data.HashSet (HashSet)
import Data.Range ( Range )
import Data.Sequence (Seq)
import Data.Hashable
import Data.L

import GHC.Generics (Generic)

import Presyntax.Context
import GHC.Stack


data Visibility = Visible | Invisible
  deriving (Eq, Show, Ord, Generic, Hashable)

data Binder t a =
  Binder { var        :: a
         , visibility :: Visibility
         , domain     :: t a
         }
  deriving (Eq, Ord, Generic, Hashable, Show)

data Term a
  -- Both impredicative universes, with Prop : Set and Set : Set (unfortunately)
  = Set | Prop
  | Pi (Binder Term a) (Term a)
  | Lam (Binder Term a) (Term a)
  | Elim  (Elim a)

  -- Interaction stuff:
  | SpannedTerm (L (Term a))
  deriving (Eq, Ord, Generic, Hashable)

data Elim a
  = Var a
  | Con a
  | Meta (Meta a)
  | App (Elim a) (Term a)
  | Cut (Term a) (Term a)
  deriving (Eq, Ord, Generic, Hashable)

data Meta a
  = MV { metaId          :: a
       , metaSlot        :: MVar (Value a)
       , metaBlockedEqns :: MVar (Seq (Constraint a))
       , metaLocation    :: Range
       , metaExpected    :: Value a
       , metaTelescope   :: [Binder Value a]
       , metaContext     :: Maybe SyntaxContext
       }
  deriving (Eq)

data Value var
  = VNe (Neutral var)
  | VFn (Binder Value var) (Value var -> Value var)
  | VPi (Binder Value var) (Value var -> Value var)
  | VSet
  | VProp

data Neutral var
  = NVar var
  | NCon var
  | NMeta (Qtt.Meta var)
  | NApp (Neutral var) (Seq (Value var))
  deriving (Eq)

data Constraint var
  = Equation { equationMeta  :: Meta var
             , equationSpine :: Seq (Value var)
             , equationRHS   :: Value var
             }
  deriving (Eq)

data Sort = SSet | SProp
  deriving (Eq, Show, Ord)


quantify :: [Binder Term var] -> Term var -> Term var
quantify [] t     = t
quantify (b:qs) r = Pi b (quantify qs r)

valueVar :: var -> Value var
valueVar = VNe . NVar

quoteNeutral :: Eq var => Neutral var -> Qtt.Elim var
quoteNeutral (NVar v) = Qtt.Var v
quoteNeutral (NCon v) = Qtt.Con v
quoteNeutral (NMeta v) = Qtt.Meta v
quoteNeutral (NApp f x) = foldl Qtt.App (quoteNeutral f) (fmap quote x)

quote :: Eq var => Value var -> Qtt.Term var
quote (VFn bind@Binder{var} b) =
  case body of
    VNe (NApp f sp) | Just n <- etaReduceMaybe f sp var -> Elim (quoteNeutral n)
    _ -> Lam bind{domain = quote (domain bind)} (quote body)
  where body = b (valueVar var)
quote (VPi binder range) =
  Qtt.Pi binder{ domain = quote (domain binder) } (quote (range (valueVar (var binder))))
quote VSet = Qtt.Set
quote VProp = Qtt.Prop
quote (VNe v) = Qtt.Elim (quoteNeutral v)

(@@) :: (HasCallStack, Eq var, Show var) => Value var -> Value var -> Value var
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
  go Con{} = False
  go (Cut a b) = isVarAlive var a || isVarAlive var b
isVarAlive _ Prop{} = False
isVarAlive _ Set{} = False
isVarAlive var (Lam Binder{var=v,domain=d} b) =
  isVarAlive var d || (v /= var && isVarAlive var b)
isVarAlive var (Pi binder@Binder{var=v} r) =
  isVarAlive var (domain binder) || (v /= var && isVarAlive var r)
isVarAlive var (SpannedTerm x) = isVarAlive var (extract x)

etaReduceMaybe :: Eq var => Neutral var -> Seq (Value var) -> var -> Maybe (Neutral var)
etaReduceMaybe f spine var =
  case Seq.viewr spine of
    sp Seq.:> v | v == valueVar var, not (isVarAlive var (Elim (quoteNeutral (NApp f sp)))) ->
      Just (NApp f sp)
    _ -> Nothing

nonLocalVars :: (Hashable var, Eq var) => Term var -> HashSet var
nonLocalVars = goTerm mempty mempty where
  goTerm !scope !free (Elim t) = goNeutral scope free t
  goTerm !scope !free (Lam Binder{var = v, domain = d} t) =
    goTerm (HashSet.insert v scope) (goTerm scope free d) t
  goTerm !scope !free (Pi (Binder{var = v, domain = d}) r) =
    goTerm (HashSet.insert v scope) (goTerm scope free d) r
  goTerm !_ !x Set = x
  goTerm !_ !x Prop = x
  goTerm !scope !free (SpannedTerm s) = goTerm scope free (extract s)

  goNeutral !scope !free (Var v)
    | HashSet.member v scope = free
    | otherwise = HashSet.insert v free
  goNeutral !_ !free (Con v) = HashSet.insert v free
  goNeutral !_ !free Meta{} = free
  goNeutral !scope !free (Cut a b) = goTerm scope (goTerm scope free a) b
  goNeutral !scope !free (App f x) = goTerm scope (goNeutral scope free f) x


metaGoal :: Meta a -> Value a
metaGoal meta =
  let dropT (Binder{Qtt.var = v}:bs) (VPi _ rng) = dropT bs (rng (valueVar v))
      dropT [] t = t
      dropT _ _ = undefined
   in dropT (metaTelescope meta) (metaExpected meta)

instance (Eq a, Show a) => Show (Term a) where
  showsPrec prec ex =
    case ex of
      Lam Binder{var=x} p ->
        showParen (prec >= 1) $
          showChar 'λ' . showChar ' ' . shows x . showString " → " . showsPrec 0 p
      Pi (Binder var vis d) r
        | isVarAlive var r ->
          showParen (prec >= 1) $
            showBracket vis
              (shows var . showString " : " . showsPrec 0 d)
            . showString " -> "
            . shows r
        | otherwise -> showParen (prec >= 1) $ showsPrec 1 d . showString " -> " . showsPrec (prec - 1) r
      Set    -> showString "Type"
      Prop   -> showString "Prop"
      Elim e -> showsPrec prec e
      SpannedTerm t -> showsPrec prec (extract t)
    where showBracket Visible k = showParen True k
          showBracket Invisible k = showChar '{' . k . showChar '}'

instance (Eq a, Show a) => Show (Elim a) where
  showsPrec _ (Var x) = shows x
  showsPrec _ (Con x) = shows x
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

instance Hashable a => Hashable (Meta a) where
  hashWithSalt s mv = hashWithSalt s (metaId mv)

instance Ord a => Ord (Constraint a) where
  compare (Equation a _ _) (Equation b _ _) = compare a b

instance (Show var, Eq var) => Show (Constraint var) where
  show (Equation m s r) = show m ++ " " ++ show s ++ " ≡? " ++ show r

instance (Hashable var, Eq var) => Hashable (Value var) where
  hashWithSalt s = hashWithSalt s . quote

instance (Eq var, Show var) => Show (Value var) where
  show = show . quote
  showsPrec p = showsPrec p . quote

instance Eq var => Eq (Value var) where
  VNe a == VNe b = a == b
  VFn Binder{var} body == VFn _ body' =
    body (valueVar var) == body' (valueVar var)
  VPi binder body == VPi binder' body' =
       domain binder == domain binder'
    && body (valueVar (var binder)) == body' (valueVar (var binder))
  VSet == VSet = True
  VProp == VProp = True
  _ == _ = False

instance (Show var, Eq var) => Show (Neutral var) where
  show = show . quoteNeutral
  showsPrec p = showsPrec p . quoteNeutral