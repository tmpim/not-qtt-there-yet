{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE FlexibleContexts #-}
module Check where

import Check.Subsumes ( subsumes, isPiType )
import Check.TypeError ( TypeError(..) )
import Check.Fresh
import Check.Monad
import Check.Data

import Control.Monad.Reader

import qualified Data.HashMap.Strict as Map
import qualified Data.Sequence as Seq
import qualified Data.HashSet as Set
import qualified Data.Text as T
import qualified Data.L as P
import Data.Sequence (Seq)
import Data.Traversable
import Data.Foldable

import Driver.Query

import qualified Presyntax as P
import Presyntax.Context

import Qtt.Environment hiding (assume)
import Qtt.Evaluate
import Qtt
import Control.Comonad (Comonad(extract))



checkLoc :: TypeCheck a m => P.ExprL a -> Value a -> m (Term a)
checkLoc t v = withLocation t $ flip checkRaw v

checkRaw :: TypeCheck a m => P.Expr P.L a -> Value a -> m (Term a)
checkRaw v (VPi b@Binder{visibility=Invisible} rng) | not (implicitLam v)
  = do assume (var b) (domain b) $ do
        tm <- checkRaw v (rng (valueVar (var b)))
        pure (Lam b{ domain = quote (domain b) } tm)
  where
    implicitLam (P.Lam v _ _) = v == Invisible
    implicitLam _ = False
    
checkRaw P.Set value = do
  p <- isSet value
  case p of
    SSet -> pure Set
    SProp -> error "Set ¬: Prop"

checkRaw (P.Lam vis binder body) term = do
  let var = P.lThing binder
  (dom, range, _wp) <- isPiType vis (Just var) term
  term <-
    inContext BodyContext $ do
      -- Add the binder to the variable IntervalMap
      withLocation binder $ \_ -> attachTypeToLoc dom

      assume var dom $
        checkLoc body (range (valueVar var))
  pure (Lam Binder{var, visibility = vis, domain = quote dom} term)

checkRaw (P.Pi vis binder domain range) i = do
  let var = P.lThing binder
  sort <- isSet i
  let dr = case sort of
             SSet -> VSet
             SProp -> VProp
  term <- checkLoc domain dr
  domain <- evaluate term

  -- Add the binder to the variable IntervalMap
  withLocation binder $ \_ -> attachTypeToLoc domain

  assume var domain $ do
    range <- inContext BodyContext $ checkLoc range dr
    pure (Pi (Binder var vis term) range)

checkRaw P.Hole ty = do
  attachTypeToLoc ty
  m <- freshMeta ty
  pure (quote m)

checkRaw P.Prop ty = do
  attachTypeToLoc ty
  _ <- isSet ty
  pure Prop

checkRaw exp expected = do
  (term, ty) <- inferRaw exp
  w <- subsumes ty expected
  nf <- evaluateNeutral term
  pure (quote (w nf))

inferLoc :: TypeCheck a m => P.ExprL a -> m (Elim a, Value a)
inferLoc ex = withLocation ex inferRaw

inferRaw :: TypeCheck a m => P.Expr P.L a -> m (Elim a, Value a)
inferRaw (P.Var a) = do
  isc <- isConstructor a
  t <- lookupVariable a
  attachTypeToLoc t
  pure ( if isc then Con a else Var a
       , t )

inferRaw (P.App t a b) = do
  (elimA, tyA) <- inContext FunctionContext $ inferLoc a
  (dom, range, wp) <- isPiType t Nothing tyA
  termB <- inContext ArgumentContext $ checkLoc b dom
  nfB <- evaluate termB
  pure (wp elimA `App` termB, range nfB)
  
inferRaw (P.Cut a b) = do
  tyB <- checkLoc b VSet
  nfB <- evaluate tyB
  tA <- checkLoc a nfB
  pure (Cut tA tyB, nfB)

inferRaw P.Hole = do
  ty <- freshMeta VSet
  ~(VNe tm) <- freshMeta ty
  pure (quoteNeutral tm, ty)

inferRaw P.Set = pure (Cut Set Set, VSet)
inferRaw P.Prop = pure (Cut Prop Set, VSet)

inferRaw e = do
  x <- freshMeta VSet
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
  nf_c <- recover VSet $ do
    c <- checkLoc ty VSet
    evaluate c
  pure ( assume var nf_c
       . local (\x -> x { unproven = Map.insert var (P.L () (P.lRange ty)) (unproven x)
                        , toplevel = Set.insert var (toplevel x) }))

checkDeclRaw (P.Value var dec) = do
  let prove x = x { unproven = Map.delete var (unproven x)
                  , toplevel = Set.insert var (toplevel x) }
  ty <- lookupType var
  case fmap P.lThing ty of
    Just sig -> do
      c <- recoverQ sig $ checkLoc dec sig
      nf_c <- evaluate c
      pure (local (insertDecl var nf_c . prove))
    Nothing -> do
      (t, ty) <- inferLoc dec
      nf_c <- evaluate (Elim t)
      pure (declare var (ty <$ dec) nf_c . local prove)

checkDeclRaw (P.DataStmt (P.DataDecl name dataParams dataKind dataCons)) = do
  local (\x -> x { currentlyChecking = Just name, constructors = Set.insert name (constructors x) }) $ do
    let eliminator = derive ".elim" name
    loc <- P.L () <$> asks (head . locationStack)

    params <- checkTelescope dataParams $ \x -> do
      let (name, sort) = extract x
      sort <- checkLoc sort VSet
      sort_nf <- evaluate sort
      pure (name, sort_nf <$ x)

    let param_pi_tel v = fmap (\(a, b) -> Binder a v (quote (P.lThing b))) params

    (sorts, the_data) <- assuming params $ do
      kind <- checkLoc dataKind VSet
      kind_nf <- evaluate kind
      closed <- evaluate (quantify (param_pi_tel Visible) kind)

      constrs <- assume name closed . local (\x -> x { constructors = Set.insert name (constructors x)}) $ do
        for dataCons . flip withLocation $ \(name, sort) -> do
          sort <- checkLoc sort VSet
          sort_nf <- evaluate sort
          pure (name, sort, sort_nf)
      
      visibleSorts <- traverse (\(a, b, _) -> (,) a <$> evaluate (quantify (param_pi_tel Invisible) b)) constrs
      pure ((name, closed):visibleSorts, Data name (fmap P.lThing <$> params) kind_nf (map (\(a, _, b) -> (a, b)) constrs))

    fakeCons <- for dataCons . flip withLocation $ \(name, _) -> do
      pure (constN params (VNe (NCon name)))

    induction <- makeInductionPrinciple the_data
    recursor <- makeRecursor eliminator the_data

    pure ( assume name (snd (head sorts))
         . foldr (\((a, b), c) r -> declare a (b <$ loc) c . r) id (zip (tail sorts) fakeCons)
         . declare eliminator (induction <$ loc) recursor
         . local (\x -> x { toplevel     = Set.union (Set.fromList (eliminator:map fst sorts)) (toplevel x)
                          , constructors = Set.union (Set.fromList (map fst sorts)) (constructors x) })
         )

checkDeclRaw (P.Include file) = do
  theirs <- fetchTC (ModuleEnv (T.unpack (P.lThing file)))
  let go ours =
        ours { assumptions  = Map.union (assumptions theirs) (assumptions ours)
             , declarations = Map.union (declarations theirs) (declarations ours)
             , constructors = Set.union (constructors theirs) (constructors ours)
             , unproven     = Map.union (unproven theirs) (unproven ours)
             , toplevel     = Set.union (toplevel theirs) (toplevel ours)
             }
  pure (local go)

constN :: Comonad w => [(var, w (Value var))] -> Value var -> Value var
constN [] x          = x
constN ((v, t):bs) x = VFn Binder{ var = v, visibility = Visible, domain = extract t } (const (constN bs x))

checkTelescope :: (TypeCheck var m, Comonad w) => [a] -> (a -> m (var, w (Value var))) -> m [(var, w (Value var))]
checkTelescope [] _ = pure []
checkTelescope (this:rest) cont = do
  (name, kind) <- cont this
  assume name (extract kind) $
    (:) (name, kind) <$> checkTelescope rest cont

checkProgram :: TypeCheck var m => [P.L (P.Decl P.L var)] -> m b -> m b
checkProgram [] kont = do
  unp <- asks unproven
  unless (Map.null unp) $ do
    for_ (Map.toList unp) $ \(m, loc) -> do
      withLocation loc $ \() -> typeError (Undefined m)
  kont
checkProgram (d:ds) kont = flip id (checkProgram ds kont) =<< checkDeclLoc d

isSet :: TypeCheck a m => Value a -> m Sort
isSet VSet  = pure SSet
isSet VProp = pure SProp
isSet t     = typeError (NotSet t)
