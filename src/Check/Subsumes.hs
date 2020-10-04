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

subsumes (VPi binder rng) (VPi binder' rng') | visibility binder == visibility binder' = do
  coe <- subsumes (domain binder') (domain binder)
  var <- fresh
  assume var (domain binder) $ do
    let cast = coe (valueVar var)
    rng <- subsumes (rng cast) (rng' (valueVar var))
    pure (\vl -> VFn var (\b -> rng (vl @@ (coe b))))

subsumes (VPi b@Binder{visibility=Invisible} range) r = do
  m <- freshMeta (domain b)
  assume (var b) (domain b) $ do
    w <- subsumes (range m) r
    pure (\vl -> w (vl @@ m))

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
    subsumesTelescope (VPi binder range) (a Seq.:<| as) (b Seq.:<| bs) = do
      subsumes a b
      new <- refresh (var binder)
      assume new (domain binder) $
        subsumesTelescope (range (valueVar new)) as bs
    subsumesTelescope t (a Seq.:<| as) (b Seq.:<| bs) = do
      subsumes a b
      subsumesTelescope t as bs

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
            liftIO . putStrLn $ "*** Solved: " ++ show (NApp (NMeta meta) spine) ++ " with " ++ show fakeLam
            liftIO $ putMVar metaSlot (quote fakeLam)
            t <- liftIO $ swapMVar metaBlockedEqns mempty
            for_ t $ \(Equation meta spine val) -> do
              solve meta spine val
            pure id
          Just t -> do
            tv <- evaluate t
            subsumes (foldl (@@) tv spine) =<< evaluate (quote (foldl (@@) fakeLam spine))
      `catchError` \(_, r) -> do
        m <- zonk (VNe (NApp (NMeta meta) spine))
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
checkScope set (Pi binder range) = do
  checkScope set (domain binder)
  checkScope (Set.insert (var binder) set) range
checkScope set (Lam var body) = checkScope (Set.insert var set) body
checkScope _ Set{} = pure ()

isPattern :: Ord a => Seq (Value a) -> Maybe (Set a)
isPattern = go mempty where
  go x (VNe (NVar v) Seq.:<| rest)
    | v `Set.member` x = Nothing
    | otherwise = go (Set.insert v x) rest
  go _ (_ Seq.:<| _) = Nothing
  go x Seq.Empty = Just x

sortOfKind :: forall a m. TypeCheck a m => Value a -> m (Value a)
sortOfKind (VFn _ _) = pure (VSet 0)
sortOfKind (VPi binder r) = do
  d <- sortOfKind (domain binder)
  r <- sortOfKind (r (valueVar (var binder)))
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

elimType :: TypeCheck var m
         => Neutral var
         -> m (Value var)
elimType (NVar v) = do
  t <- lookupType v
  case t of
    Nothing -> typeError (NotInScope v)
    Just t -> pure $ t
elimType (NMeta mv) = pure (metaExpected mv)
elimType (NApp f xs) = do
  kind <- elimType f
  let -- Apply actual arguments
      go (VPi _ r) (a Seq.:<| xs)
        = go (r a) xs
      -- Empty arguments: that's the type
      go t Seq.Empty  = pure t
      -- Anything else, we've screwed up
      go t (a Seq.:<| as) = error (show (NApp f xs, kind, t, a, as))
  go kind xs
elimType NProp = pure $ VSet 1

isPiType :: TypeCheck a m
         => Visibility    -- What visibility of Π do we need?
         -> Maybe a
         -> Value a
         -> m ( Value a
              , Value a -> Value a
              , Elim a -> Elim a
              )
isPiType Visible   _ (VPi Binder{visibility = Visible, domain = a} b)   = pure (a, b, id)
isPiType Invisible _ (VPi Binder{visibility = Invisible, domain = a} b) = pure (a, b, id)

isPiType Visible hint (VPi Binder{visibility = Invisible, domain = dom } rng) = do
  meta <- freshMeta dom
  (domain, range, inner) <- isPiType Visible hint (rng meta)
  pure (domain, range, \x -> inner (App x (quote meta)))

isPiType _ _ ty@VSet{} = typeError (NotPi ty)
isPiType _ _ ty@VFn{} = typeError (NotPi ty)
isPiType over hint t = do
  name <- case hint of
    Just t -> pure t
    Nothing -> fresh
  domain <- freshMeta (VSet maxBound)
  assume name domain $ do
    range <- freshMeta (VSet maxBound)
    let binder = Binder { var = name
                        , domain = domain
                        , visibility = over
                        }
    subsumes t (VPi binder (const range))
    pure (domain, const range, id)