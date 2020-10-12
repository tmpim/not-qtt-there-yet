{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Check.Monad where

import Check.TypeError
import Check.Fresh

import Control.Concurrent (putMVar, tryTakeMVar, tryReadMVar, modifyMVar_, newMVar, newEmptyMVar)
import Control.Exception (Exception, catch)
import Control.Monad.Trans.Control
import Control.Monad.Writer.Strict
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.Base

import qualified Data.IntervalMap.FingerTree as IntervalMap
import qualified Data.HashMap.Compat as Map
import qualified Data.HashSet as HashSet
import qualified Data.Sequence as Seq
import qualified Data.HashSet as Set
import Data.HashSet (HashSet)
import Data.Sequence (Seq)
import Data.Range

import Driver.Query

import Qtt.Environment
import Qtt.Builtin
import Qtt

import Rock (fetch, Task, MonadFetch)

import Type.Reflection ( Typeable )


type TypeCheck var m =
  ( Fresh var, Typeable var -- var is a variable type
  , MonadReader (Env var) m
  , MonadError (TypeError var, [Range]) m
  , MonadIO m
  , MonadFetch (Query var) m

  , MonadBase IO m
  , MonadBaseControl IO m
  )

defer :: TypeCheck var m => Meta var -> Seq (Value var) -> Value var -> m ()
defer m s r =
  do
    slot <- asks deferredEqns
    deferred <- liftIO (tryTakeMVar slot)
    liftIO $
      case deferred of
        Just map -> putMVar slot (insert m (Equation m s r) map)
        Nothing -> putMVar slot (Map.singleton m (Seq.singleton (Equation m s r)))
  where
    insert key eq = Map.alter (go eq) key

    go eq Nothing = Just (Seq.singleton eq)
    go eq (Just s) = Just (s Seq.:|> eq)

freshMeta :: (MonadReader (Env a) m, MonadIO m, Fresh a, Ord a, Show a)
          => Value a -> m (Value a)
freshMeta expected = do
  id <- fresh
  top <- asks toplevel
  tele <- asks (Map.toList . flip Map.withoutKeys top . assumptions)
  loc <- asks locationStack

  ctx <- asks syntaxContext

  let quantify ((a, b):xs) t = VPi Binder{ visibility = Visible, domain = b, var = a } (\_ -> quantify xs t)
      quantify [] t = t

      teleify = map (\(a, b) -> Binder { visibility = Visible, domain = b, var = a })

  meta <- liftIO $ MV id -- metavariable identifier
               <$> newEmptyMVar -- metavariable solution
               <*> newMVar mempty -- eqns blocked on this meta
               <*> pure (head loc)
               <*> pure (quantify tele expected)
               <*> pure (teleify tele)
               <*> pure ctx

  unsolved <- asks unsolvedMetas
  liftIO . modifyMVar_ unsolved $ pure . Set.insert meta
  pure (VNe (NApp (NMeta meta) (fmap valueVar (Seq.fromList (map fst tele)))))

newtype TCM var a
  = TCM { runChecker :: Env var -> Rock.Task (Query var) (Either (TypeError var, [Range]) a) }
  deriving ( Functor
           , Applicative
           , Monad
           , MonadReader (Env var)
           , MonadError (TypeError var, [Range])
           , MonadFetch (Query var)
           , MonadBase IO
           , MonadBaseControl IO
           , MonadIO
           )
    via (ReaderT (Env var) (ExceptT (TypeError var, [Range]) (Task (Query var))))

getUnsolvedMetas :: TypeCheck var m => m (HashSet (Meta var))
getUnsolvedMetas = do
  mv <- asks unsolvedMetas
  t <- liftIO $ tryReadMVar mv
  pure $
    case t of
      Nothing -> mempty
      Just set -> set

typeError :: TypeCheck var m => TypeError var -> m b
typeError e = do
  c <- asks locationStack
  throwError (e, c)

fetchTC :: forall m var a. TypeCheck var m => Query var a -> m a
fetchTC query = control $ \runInIO ->
  catch (runInIO (Rock.fetch query)) $
        \case
          Tee e -> runInIO (typeError e :: m a)
          Teer e r -> runInIO (throwError (e, r) :: m a)

findBuiltin :: forall m var kit. TypeCheck var m => Builtin var kit -> m kit
findBuiltin b = fetchTC (MakeBuiltin b)

recover :: forall m var. TypeCheck var m
        => Value var
        -> m (Value var)
        -> m (Value var)
recover expectedType comp =
  catchError comp $
    \(error, loc) -> do
       ref <- asks recoveredErrors
       liftIO $ modifyMVar_ ref (pure . HashSet.insert (error, loc))
       fail <- findBuiltin BuiltinFail
       pure (builtinValue fail @@ expectedType)

recoverQ :: forall m var. TypeCheck var m
         => Value var
         -> m (Term var)
         -> m (Term var)
recoverQ expectedType comp =
  catchError comp $
    \(error, loc) -> do
       ref <- asks recoveredErrors
       liftIO $ modifyMVar_ ref (pure . HashSet.insert (error, loc))
       fail <- findBuiltin BuiltinFail
       pure (Elim (App (Var (builtinName fail)) (quote expectedType)))

lookupVariable :: forall m var. TypeCheck var m => var -> m (Value var)
lookupVariable v = do
  t <- asks (Map.lookup v . assumptions)
  case t of
    Just ty -> pure ty
    Nothing -> typeError (NotInScope v)

isConstructor :: forall m var. TypeCheck var m => var -> m Bool
isConstructor v = asks (Set.member v . constructors)

attachTypeToLoc :: forall m var. TypeCheck var m => Value var -> m ()
attachTypeToLoc ty = do
  t <- ask
  let int = rangeToInterval (head (locationStack t))
  liftIO . modifyMVar_ (interestingIntervals t) $ pure . IntervalMap.insert int ty

data TypeErrorException var = Tee (TypeError var) | Teer (TypeError var) [Range]
  deriving (Eq, Show, Exception)