{-# LANGUAGE FlexibleContexts #-}
module Check where

import Control.Monad.Reader

import Data.Traversable
import Data.Foldable

import qualified Presyntax as P

import Qtt.Environment
import Qtt.Evaluate
import Qtt

import Check.TypeError ( TypeError(..) )
import Check.Subsumes ( subsumes, isPiType )
import Check.Monad
import Check.Fresh
import Check.Data

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq

checkLoc :: TypeCheck a m => P.ExprL a -> Value a -> m (Term a)
checkLoc t v = withLocation t $ \ex -> checkRaw ex v

checkRaw :: TypeCheck a m => P.Expr P.L a -> Value a -> m (Term a)
checkRaw v (VPi b@Binder{visibility=Invisible} rng) | not (implicitLam v)
  = do
    assume (var b) (domain b) $ do
      tm <- checkRaw v (rng (valueVar (var b)))
      pure (Lam (var b) tm)
  where
    implicitLam (P.Lam v _ _) = v == Invisible
    implicitLam _ = False
    
checkRaw (P.Set j) value = do
  i <- isSet value
  unless (j < i) $
    typeError (TypeTooBig j i)
  pure (Set j)

checkRaw l@(P.Lam vis var body) term = do
  liftIO . putStrLn $ "Checking lambda " ++ show l ++ " against " ++ show term
  (dom, range, _wp) <- isPiType vis (Just var) term
  term <-
    assume var dom $
      checkLoc body (range (valueVar var))
  pure (Lam var term)

checkRaw (P.Pi vis var domain range) prop@(VNe NProp) = do
  term <- checkLoc domain prop
  domain <- evaluate term
  assume var domain $ do
    range <- checkLoc range prop
    pure (Pi (Binder var vis term) range)

checkRaw (P.Pi vis var domain range) i = do
  i <- isSet i
  term <- checkLoc domain (VSet i)
  domain <- evaluate term
  assume var domain $ do
    range <- checkLoc range (VSet i)
    pure (Pi (Binder var vis term) range)

checkRaw P.Hole ty = do
  m <- freshMeta ty
  pure (quote m)

checkRaw P.Prop (VNe NProp) = do
  pure $ Elim Prop

checkRaw P.Prop ty = do
  _ <- isSet ty
  pure $ Elim Prop

checkRaw exp expected = do
  (term, ty) <- inferRaw exp
  w <- subsumes ty expected
  nf <- evaluateNeutral term
  pure (quote (w nf))

inferLoc :: TypeCheck a m => P.ExprL a -> m (Elim a, Value a)
inferLoc ex = withLocation ex inferRaw

inferRaw :: TypeCheck a m => P.Expr P.L a -> m (Elim a, Value a)
inferRaw (P.Var a) = do
  t <- lookupType a
  case t of
    Just ty -> pure (Var a, ty)
    Nothing -> typeError (NotInScope a)

inferRaw (P.App t a b) = do
  (elimA, tyA) <- inferLoc a
  (dom, range, wp) <- isPiType t Nothing tyA
  termB <- checkLoc b dom
  nfB <- evaluate termB
  pure (wp elimA `App` termB, range nfB)
  
inferRaw (P.Cut a b) = do
  tyB <- checkLoc b (VSet 0)
  nfB <- evaluate tyB
  tA <- checkLoc a nfB
  pure (Cut tA tyB, nfB)

inferRaw P.Hole = do
  ty <- freshMeta (VSet maxBound)
  ~(VNe tm) <- freshMeta ty
  pure (quoteNeutral tm, ty)

inferRaw (P.Set i) = pure (Cut (Set i) (Set (i + 1)), VSet (i + 1))
inferRaw P.Prop = pure (Prop, VSet 1)

inferRaw e = do
  x <- freshMeta (VSet maxBound)
  term <- checkRaw e x
  pure (Cut term (quote x), x)

instantiate :: TypeCheck a m => Value a -> m (Seq (Value a), Value a)
instantiate (VPi Binder{domain = dom} range) = do
  meta <- freshMeta dom
  (seq, r) <- instantiate (range meta)
  pure (seq Seq.:|> meta, r)
instantiate t = pure (mempty, t)

checkDeclLoc :: TypeCheck var m => P.L (P.Decl P.L var) -> m (m b -> m b)
checkDeclLoc = flip withLocation checkDeclRaw

checkDeclRaw :: TypeCheck var m => P.Decl P.L var -> m (m b -> m b)
checkDeclRaw (P.TypeSig var ty) = do
  c <- checkLoc ty (VSet maxBound)
  nf_c <- evaluate c
  pure ( assume var nf_c
       . local (\x -> x { unproven = Map.insert var (P.L () (P.lRange ty)) (unproven x)
                        , toplevel = Set.insert var (toplevel x) }))

checkDeclRaw (P.Value var dec) = do
  let prove x = x { unproven = Map.delete var (unproven x)
                  , toplevel = Set.insert var (toplevel x) }
  ty <- lookupType var
  case ty of
    Just sig -> do
      c <- checkLoc dec sig
      nf_c <- evaluate c
      pure (local (insertDecl var nf_c . prove))
    Nothing -> do
      (t, ty) <- inferLoc dec
      nf_c <- evaluate (Elim t)
      pure (declare var ty nf_c . local prove)

checkDeclRaw (P.DataDecl name dataParams dataKind constructors) = do
  let eliminator = derive ".elim" name

  params <- checkTelescope dataParams . flip withLocation $ \(name, sort) -> do
    sort <- checkLoc sort (VSet maxBound)
    sort_nf <- evaluate sort
    pure (name, sort_nf)
  let param_pi_tel v = fmap (\(a, b) -> Binder a v (quote b)) params

  (sorts, the_data) <- assuming params $ do
    kind <- checkLoc dataKind (VSet maxBound)
    kind_nf <- evaluate kind
    l <-
      case kind_nf of
        -- In case the return kind of the data type is Prop,
        -- any sort is allowed in the parameters.
        -- This does not cause inconsistency because Prop can
        -- only be eliminated into Prop.
        VNe NProp -> pure Nothing
        -- Otherwise, get a valid level.
        _ -> fmap Just . withLocation dataKind $ \_ -> isSet (snd (splitPi_pure kind_nf))
    closed <- evaluate (quantify (param_pi_tel Visible) kind)
    
    -- now that we know the level of the data type we need to go back and check all of the parameters
    -- ... again ...
    _ <- case l of
      Just l ->
        checkTelescope dataParams . flip withLocation $ \(name, sort) -> do
          sort <- checkLoc sort (VSet (succ l))
          sort_nf <- evaluate sort
          pure (name, sort_nf)
      Nothing -> pure []

    constrs <- assume name closed $ do
      for constructors . flip withLocation $ \(name, sort) -> do
        sort <- case l of
          -- When eliminating into Type_l: ensure that size restrictions are
          -- respected
          Just l  -> checkLoc sort (VSet l)
          -- When eliminating into Prop: size issues don't matter
          Nothing -> checkLoc sort (VSet maxBound)
        sort_nf <- evaluate sort
        pure (name, sort, sort_nf)
    
    visibleSorts <- traverse (\(a, b, _) -> (,) a <$> evaluate (quantify (param_pi_tel Invisible) b)) constrs
    pure ((name, closed):visibleSorts, Data name params kind_nf (map (\(a, _, b) -> (a, b)) constrs))

  fakeCons <- for constructors . flip withLocation $ \(name, _) -> do
    ignored <- refresh name
    pure (constN ignored (length params) (valueVar name))

  induction <- makeInductionPrinciple the_data
  recursor <- makeRecursor eliminator the_data

  pure ( assume name (snd (head sorts))
       . foldr (\((a, b), c) r -> declare a b c . r) id (zip (tail sorts) fakeCons)
       . declare eliminator induction recursor
       . local (\x -> x { toplevel = Set.union (Set.fromList (eliminator:map fst sorts)) (toplevel x) }))

const' :: var -> Value var -> Value var
const' x v = VFn x (const v)

constN :: Fresh var => var -> Int -> Value var -> Value var
constN _ 0 x = x
constN var n x = const' var (constN var (n - 1) x)

checkTelescope :: TypeCheck var m => [a] -> (a -> m (var, Value var)) -> m [(var, Value var)]
checkTelescope [] _ = pure []
checkTelescope (this:rest) cont = do
  (name, kind) <- cont this
  assume name kind $
    (:) (name, kind) <$> checkTelescope rest cont

checkProgram :: TypeCheck var m => [P.L (P.Decl P.L var)] -> m b -> m b
checkProgram [] kont = do
  unp <- asks unproven
  unless (Map.null unp) $ do
    for_ (Map.toList unp) $ \(m, loc) -> do
      liftIO . print =<< lookupType m
      withLocation loc $ \() -> typeError (Undefined m)

  kont
checkProgram (d:ds) kont = flip id (checkProgram ds kont) =<< checkDeclLoc d


isSet :: TypeCheck a m => Value a -> m Int
isSet (VSet i) = pure i
isSet t = typeError (NotSet t)
