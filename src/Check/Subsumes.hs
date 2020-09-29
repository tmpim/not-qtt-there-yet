{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards #-}
module Check.Subsumes where

import Control.Monad.IO.Class

import qualified Data.Set as Set
import Data.Set (Set)

import Check.TypeError
import Check.Monad

import Qtt.Environment
import Qtt.Evaluate
import Qtt

import Control.Concurrent
import qualified Data.Sequence as Seq
import Data.Foldable (for_)

import Check.Fresh
import Control.Monad.Except (throwError, MonadError(catchError))
import Control.Monad.Reader (asks)

import Data.Sequence (Seq)

subsumes :: TypeCheck a m
         => Value a
         -> Value a
         -> m (Value a -> Value a)

subsumes a b | a == b = pure id

subsumes (VNe a) val
  | Just (meta, spine) <- isMeta a = solve meta spine val

subsumes val (VNe a)
  | Just (meta, spine) <- isMeta a = solve meta spine val

subsumes (VPi _ vis dom rng) (VPi _ vis' dom' rng') | vis == vis' = do
  liftIO . print $ (dom', dom)
  coe <- subsumes dom' dom
  var <- fresh
  assume var dom $ do
    let cast = coe (valueVar var)
    rng <- subsumes (rng cast) (rng' (valueVar var))
    pure (\vl -> VFn var (\b -> rng (vl @@ (coe b))))

-- λx. e ≡ g → e ≡ g x
subsumes (VFn var k) b =
  subsumes (k (valueVar var)) (b @@ valueVar var)

subsumes (VNe a) (VNe b) = do
  t <- elimType a
  subsumesNe t a b

subsumes (VNe NProp) (VSet j)
  | j >= 1 = pure id

subsumes (VSet i) (VSet j)
  | i <= j = pure id

subsumes a b = typeError (NotEqual a b)

isMeta :: Neutral a -> Maybe (Meta a, Seq (Value a))
isMeta (NMeta m) = pure (m, Seq.empty)
isMeta (NApp (NMeta m) t) = pure (m, t)
isMeta _ = Nothing

sortOfKind :: forall a m. TypeCheck a m => Value a -> m (Value a)
sortOfKind (VFn _ _) = pure (VSet 0)
sortOfKind (VPi v _ d r) = do
  d <- sortOfKind d
  r <- sortOfKind (r (valueVar v))
  liftIO $ print (d, r)
  case (d, r) of
    (VNe NProp, _) -> pure (VNe NProp)
    (_, VNe NProp) -> pure (VNe NProp)
    (VSet a, VSet b) -> pure (VSet (max a b))
sortOfKind (VSet i) = pure (VSet (i + 1))
sortOfKind (VNe a) =
  case a of
    NVar t -> do
      ty <- lookupType t
      case ty of
        Just k -> pure k
        Nothing -> typeError (NotInScope t)
    NMeta t -> sortOfKind (metaExpected t)
    NProp -> pure (VSet 1)
    NApp v t -> elimType (NApp v t)

subsumesNe :: forall a m. TypeCheck a m
           => Value a
           -> Neutral a
           -> Neutral a
           -> m (Value a -> Value a)
subsumesNe kind a b =
  do
    sort <- sortOfKind kind
    case sort of
      -- All values in types in Prop are equal
      VNe NProp -> pure id
      _ -> go a b
  where
    go (NVar a) (NVar b) | a == b = pure id
    go (NApp h t) (NApp h' t') | h == h', length t == length t' = do
      hKind <- elimType h
      id <$ subsumesTelescope hKind t t'
    go x y = typeError (NotEqual (VNe x) (VNe y))

    subsumesTelescope :: Value a -> Seq (Value a) -> Seq (Value a) -> m ()
    subsumesTelescope _ Seq.Empty Seq.Empty = pure ()
    subsumesTelescope (VPi var _ dom range) (a Seq.:<| as) (b Seq.:<| bs) = do
      subsumes a b
      new <- refresh var
      assume new dom $
        subsumesTelescope (range (valueVar new)) as bs

solve :: TypeCheck a m
      => Meta a
      -> Seq (Value a)
      -> Value a
      -> m (Value a -> Value a)
solve meta@MV{..} spine val
  | Just MV{..} <- metaHeaded val =
      fmap (const id) . liftIO . modifyMVar_ metaBlockedEqns $ \queue ->
        pure (queue Seq.:|> Equation meta spine val)
  | Just vars <- isPattern spine =
      do
        val <- quote <$> zonk val
        top <- asks toplevel
        checkScope (top <> vars) val
        fakeLam <- evaluate $ foldr (\(VNe (NVar v)) b -> Lam v b) val spine
        x <- liftIO $ tryReadMVar metaSlot
        case x of
          Nothing -> do
            solveMeta meta
            liftIO $ putMVar metaSlot (quote fakeLam)
            t <- liftIO $ swapMVar metaBlockedEqns mempty
            for_ t $ \(Equation meta spine val) -> do
              solve meta spine val
            pure id
          Just t -> do
            tv <- evaluate t
            subsumes (foldl (@@) tv spine) =<< evaluate (quote (foldl (@@) fakeLam spine))
      `catchError` \(_, r) -> do
        m <- zonk (VNe (NMeta meta))
        throwError ((NotEqual m val), r)
  | otherwise = id <$ defer meta spine val

metaHeaded :: Value a -> Maybe (Meta a)
metaHeaded (VNe (NApp (NMeta m) _)) = Just m
metaHeaded (VNe (NMeta m)) = Just m
metaHeaded _ = Nothing

checkScope :: TypeCheck a m => Set a -> Term a -> m ()
checkScope set (Elim a) = go a where
  go (Var v)
    | v `Set.member` set = pure ()
    | otherwise = typeError (NotInScope v)
  go (App a b) = do
    go a
    checkScope set b
  go (Cut a b) = do
    checkScope set a
    checkScope set b
  go Meta{} = pure ()
checkScope set (Pi var _vis domain range) = do
  checkScope set domain
  checkScope (Set.insert var set) range
checkScope set (Lam var body) = checkScope (Set.insert var set) body
checkScope _ Set{} = pure ()

isPattern :: Ord a => Seq (Value a) -> Maybe (Set a)
isPattern = go mempty where
  go x (VNe (NVar v) Seq.:<| rest)
    | v `Set.member` x = Nothing
    | otherwise = go (Set.insert v x) rest
  go _ (_ Seq.:<| _) = Nothing
  go x Seq.Empty = Just x
