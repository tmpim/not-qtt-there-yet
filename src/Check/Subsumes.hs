{-# LANGUAGE FlexibleContexts #-}
module Check.Subsumes where

import Control.Monad.IO.Class
import Control.Monad.Except (catchError, zipWithM_, throwError, MonadError)

import qualified Data.Set as Set
import Data.Set (Set)

import Check.TypeError
import Check.Monad

import Qtt.Evaluate
import Qtt

import Control.Concurrent
import qualified Data.Sequence as Seq
import Debug.Trace (traceShow, traceM)
import Data.Foldable (for_)

import Check.Fresh

subsumes :: TypeCheck a m => Value a -> Value a -> m ()
subsumes (VNe (NApp (NMeta m) spine)) term = solve m (reverse spine) term
subsumes (VNe a) (VNe b) = subsumesNe a b
subsumes (VPi _ domain range) (VPi _ domain' range') = do
  v <- fresh
  subsumes domain' domain
  subsumes (range (valueVar v)) (range' (valueVar v))
subsumes (VFn a b) t = subsumes (b (valueVar a)) (t @@ valueVar a)
subsumes (VSet i) (VSet j)
  | i <= j = pure ()
subsumes a b = throwError (NotEqual a b)

subsumesNe :: TypeCheck a m => Neutral a -> Neutral a -> m ()
subsumesNe (NVar a) (NVar b)
  | a == b = pure ()
  | otherwise = throwError (NotEqual (valueVar a) (valueVar b))
subsumesNe (NApp (NVar h) b) (NApp (NVar h') b') | h == h' = do
  zipWithM_ subsumes b b'
subsumesNe (NApp (NMeta m) spine) term = do
  term <- zonk (VNe term)
  solve m (reverse spine) term
subsumesNe a b = throwError (NotEqual (VNe a) (VNe b))

solve :: TypeCheck a m => Meta a -> [Value a] -> Value a -> m ()
solve meta spine val | traceShow (meta, spine, val) False = pure ()
solve meta@(MV _ mvar blocked) spine val
  | Just meta'@(MV _ _ blocked) <- metaHeaded val = do
      traceM $ "Solving of " ++ show (Equation meta spine val) ++ " blocked on " ++ show meta'
      liftIO . modifyMVar_ blocked $ \queue ->
        pure (queue Seq.:|> Equation meta spine val)
  | Just vars <- isPattern spine =
      do
        val <- quote <$> zonk val
        checkScope vars val
        fakeLam <- evaluate $ foldr (\(VNe (NVar v)) b -> Lam v b) val spine
        x <- liftIO $ tryReadMVar mvar
        case x of
          Nothing -> do
            solveMeta meta
            liftIO $ putMVar mvar (quote (foldl (@@) fakeLam spine))
            t <- liftIO $ swapMVar blocked mempty
            for_ t $ \(Equation meta spine val) -> do
              solve meta spine val
          Just t -> do
            tv <- evaluate t
            subsumes tv =<< evaluate (quote (foldl (@@) fakeLam spine))
      `catchError` \e -> throwError (Timing e (WhenSolving meta spine val))
  | otherwise = defer meta spine val

metaHeaded :: Value a -> Maybe (Meta a)
metaHeaded (VNe (NApp (NMeta m) _)) = Just m
metaHeaded (VNe (NMeta m)) = Just m
metaHeaded _ = Nothing

checkScope :: (Ord a, MonadError (TypeError a) m) => Set a -> Term a -> m ()
checkScope set (Elim a) = go a where
  go (Var v)
    | v `Set.member` set = pure ()
    | otherwise = throwError (NotInScope v)
  go (App a b) = do
    go a
    checkScope set b
  go (Cut a b) = do
    checkScope set a
    checkScope set b
  go Meta{} = pure ()
checkScope set (Pi var domain range) = do
  checkScope set domain
  checkScope (Set.insert var set) range
checkScope set (Lam var body) = checkScope (Set.insert var set) body
checkScope _ Set{} = pure ()

isPattern :: Ord a => [Value a] -> Maybe (Set a)
isPattern = go mempty where
  go x (VNe (NVar v):rest)
    | v `Set.member` x = Nothing
    | otherwise = go (Set.insert v x) rest
  go _ (_:_) = Nothing
  go x [] = Just x
