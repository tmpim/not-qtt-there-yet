{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards #-}
module Check.Subsumes where

import Check.TypeError
import Check.Fresh
import Check.Monad

import Control.Monad.Reader (asks)
import Control.Monad.IO.Class
import Control.Concurrent
import Control.Comonad

import qualified Data.HashMap.Compat as Map
import qualified Data.Sequence as Seq
import qualified Data.HashSet as Set
import Data.HashSet (HashSet)
import Data.Sequence (Seq)
import Data.Hashable

import Qtt.Environment hiding (assume)
import Qtt.Evaluate
import Qtt
import Data.Foldable


subsumes :: TypeCheck a m
         => Value a
         -> Value a
         -> m (Value a -> Value a)

subsumes a b | a == b = pure id

subsumes (VPi binder rng) (VPi binder' rng') | visibility binder == visibility binder' = do
  coe <- subsumes (domain binder') (domain binder)
  var <- fresh
  assume var (domain binder) $ do
    let cast = coe (valueVar var)
    rng <- subsumes (rng cast) (rng' (valueVar var))
    pure (\vl -> VFn binder (\b -> rng (vl @@ (coe b))))

subsumes (VPi b@Binder{visibility=Invisible} range) r = do
  m <- freshMeta (domain b)
  assume (var b) (domain b) $ do
    w <- subsumes (range m) r
    pure (\vl -> w (vl @@ m))

-- λx. e ≡ g → e ≡ g x
subsumes (VFn Binder{var} k) b =
  subsumes (k (valueVar var)) (b @@ valueVar var)

subsumes b (VFn Binder{var} k) =
  subsumes (b @@ valueVar var) (k (valueVar var))

subsumes (VNe a) val
  | Just (meta, spine) <- isMeta a = solve meta spine val

subsumes val (VNe a)
  | Just (meta, spine) <- isMeta a = solve meta spine val

subsumes (VNe a) (VNe b) = do
  t <- elimType a
  subsumesNe t a b

subsumes VProp VSet = pure id
subsumes VSet VSet  = pure id

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
      VProp -> pure id
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
      _ <- subsumes a b
      new <- refresh (var binder)
      assume new (domain binder) $
        subsumesTelescope (range (valueVar new)) as bs
    subsumesTelescope t (a Seq.:<| as) (b Seq.:<| bs) = do
      _ <- subsumes a b
      subsumesTelescope t as bs
    subsumesTelescope _ _ _ = error "Malformed subsumesTelescope"

solve :: TypeCheck a m => Meta a -> Seq (Value a) -> Value a -> m (Value a -> Value a)
doSolve :: TypeCheck a m => Meta a -> Seq (Value a) -> Value a -> m (Value a -> Value a)

doSolve meta@MV{..} incomingSpine incomingVal
  | Just MV{..} <- metaHeaded val = do
      fmap (const id) . liftIO . modifyMVar_ metaBlockedEqns $ \queue ->
        pure (queue Seq.:|> Equation meta spine val)
  | Just vars <- isPattern spine = do
      -- Check the scoping of the RHS
      val <- quote <$> zonk val
      checkScope vars val

      unknownT <- valueVar <$> fresh

      -- Make λ spine → rhs
      let makeLam (VNe (NVar v), t) b = Lam Binder{var = v, domain = quote t, visibility = Visible } b
          makeLam (v, _) _ = error $ "Solving metavariable not in pattern form: " ++ show v ++ " in spine"

      fakeLam <- evaluate $ foldr makeLam val $ zip (toList spine) (map domain metaTelescope ++ repeat unknownT)

      -- Solve it
      liftIO $ putMVar metaSlot fakeLam
      solveMeta meta

      pure id
  | otherwise = do
    id <$ defer meta spine val
  where (spine, val) = contractSpine incomingSpine incomingVal

solve meta spine value = do
  x <- liftIO $ tryReadMVar (metaSlot meta)
  case x of
    Just thing -> subsumes (foldl (@@) thing spine) value
    Nothing -> doSolve meta spine value

solveMeta :: TypeCheck a m => Meta a -> m ()
solveMeta meta = do
  unsolved <- asks unsolvedMetas
  liftIO . modifyMVar_ unsolved $ pure . Set.delete meta

  t <- liftIO $ swapMVar (metaBlockedEqns meta) mempty
  for_ t $ \(Equation meta spine val) -> do
    solve meta spine val

  defSlot <- asks deferredEqns
  deferred <- liftIO (takeMVar defSlot)

  case Map.lookup meta deferred of
    Just eqns -> do
      liftIO $ putMVar defSlot (Map.delete meta deferred)
      for_ eqns $ \(Equation a b c) ->
        solve a b c
    Nothing -> liftIO $ putMVar defSlot deferred

contractSpine :: Eq a => Seq (Value a) -> Value a -> (Seq (Value a), Value a)
contractSpine m_spine val@(VNe (NApp f f_spine)) =
  case (Seq.viewr m_spine, Seq.viewr f_spine) of
    (m_spine' Seq.:> VNe (NVar v), f_spine' Seq.:> VNe (NVar v'))
      | v == v' -> contractSpine m_spine' (VNe (NApp f f_spine'))
    _ -> (m_spine, val)
contractSpine x y = (x, y)

metaHeaded :: Value a -> Maybe (Meta a)
metaHeaded (VNe (NApp (NMeta m) _)) = Just m
metaHeaded (VNe (NMeta m)) = Just m
metaHeaded _ = Nothing

checkScope :: TypeCheck a m => HashSet a -> Term a -> m ()
checkScope set (Elim a) = go a where
  go (Var v)
    | v `Set.member` set = pure ()
    | otherwise = () <$ lookupVariable v
  go Con{} = pure ()
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
checkScope set (Lam Binder{var} body) = checkScope (Set.insert var set) body
checkScope _ Set{} = pure ()
checkScope _ Prop{} = pure ()
checkScope set (SpannedTerm s) = checkScope set (extract s)

isPattern :: (Ord a, Hashable a) => Seq (Value a) -> Maybe (HashSet a)
isPattern = go mempty where
  go x (VNe (NVar v) Seq.:<| rest)
    | v `Set.member` x = Nothing
    | otherwise = go (Set.insert v x) rest
  go _ (_ Seq.:<| _) = Nothing
  go x Seq.Empty = Just x

sortOfKind :: forall a m. TypeCheck a m => Value a -> m (Value a)
sortOfKind (VFn _ _) = pure VSet
sortOfKind (VPi binder r) = do
  d <- sortOfKind (domain binder)
  r <- sortOfKind (r (valueVar (var binder)))
  case (d, r) of
    (VProp, _)   -> pure VProp
    (_, VProp)   -> pure VProp
    (VSet, VSet) -> pure VSet
    (_, _) -> undefined
sortOfKind VProp = pure VSet
sortOfKind VSet = pure VSet
sortOfKind (VNe a) =
  case a of
    NVar t -> lookupVariable t
    NCon t -> lookupVariable t
    NMeta t -> sortOfKind (metaExpected t)
    NApp v t -> elimType (NApp v t)

elimType :: TypeCheck var m
         => Neutral var
         -> m (Value var)
elimType (NVar v) = lookupVariable v
elimType (NCon v) = lookupVariable v
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
isPiType Invisible _ t@(VPi Binder{visibility = Visible} _) =
  typeError (NotPi Invisible t)

isPiType Visible hint (VPi Binder{visibility = Invisible, domain = dom } rng) = do
  meta <- freshMeta dom
  (domain, range, inner) <- isPiType Visible hint (rng meta)
  pure (domain, range, \x -> inner (App x (quote meta)))

isPiType v _ ty@VSet{} = typeError (NotPi v ty)
isPiType v _ ty@VProp{} = typeError (NotPi v ty)
isPiType v _ ty@VFn{} = typeError (NotPi v ty)
isPiType over hint t@VNe{} = do
  name <- case hint of
    Just t -> pure t
    Nothing -> fresh

  domain <- freshMeta VSet

  assume name domain $ do
    range <- freshMeta VSet
    let binder = Binder { var = name
                        , domain = domain
                        , visibility = over
                        }
    _ <- subsumes t (VPi binder (const range))
    -- Justification for dropping the wrapper. By cases:
    -- if t == VNe NProp, subsumes fails
    -- if t == VNe (NVar _), subsumes fails
    -- if t == VNe (NApp (NVar _) _), subsumes fails
    -- if t == VNe (NMeta _), subsumes works and returns id
    -- if t == VNe (NApp (NMeta _) _), subsumes works and returns id
    -- therefore the wrapper is either id or unreachable
    pure (domain, const range, id)