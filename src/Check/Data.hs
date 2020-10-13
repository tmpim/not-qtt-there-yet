{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards #-}
{-

Given a data type declaration of the form:

data X Δ : τs → Set j where
  c1 : Γ → X Δ τs'
  c2 : Γ, (x : X Δ τs'), Γ' → X Δ τs''
  c3 : Γ, (f : Π Ξ, X Δ τs'), Γ' → X Δ τs''

Compute the type of the induction principle

indX : Π Δ, tel(τs), (P : τs → X Δ τs → Set j)
    -> (ec1 : Π Γ → P (c1 Γ))
    -> (ec2 : Π Γ, (x : X Δ τ'), Γ' → (px : P x) → P (c2 Γ, x, Γ))
    -> (ec3 : Π Γ, (x : Π Ξ, X Δ τ'), Γ' → (pf : Π Ξ, P (f Ξ)) → P (ec3 Γ, f, Γ'))
    -> (x : X Δ tel(τs))
    -> P x

Where:
  Γ, Γ' denotes telescope composition
  tel(τ) denotes a telescope of fresh variables binding the indices in τs
  Δ, Ξ, Γ and co denote telescopes

Additionally, compute the definition of indX.
(The implementation is unique up to function extensionality,
and its definition is entirely implied by its type.)
-}
module Check.Data where

import Check.TypeError
import Check.Subsumes
import Check.Fresh
import Check.Monad

import Control.Monad.Except (catchError, MonadError(throwError))
import Control.Monad.Identity ( Identity(runIdentity) )
import Control.Arrow

import qualified Data.Map.Strict as Map
import qualified Data.Sequence as Seq
import Data.Sequence (Seq)
import Data.Traversable
import Data.Foldable

import Qtt.Evaluate
import Qtt


data Data var =
  Data { dataName :: var
       , dataArgs :: [(var, Value var)]
       , dataKind :: Value var
       , dataCons :: [(var, Value var)]
       }
  deriving (Eq, Show)

{-
for a type like
data X Δ : τ → Set j where

the induction principle is quantified over Δ but the proposition is parametrised by a τ. Like:
indX : Δ (x : τ) (P : (x : τ) → X Δ τ → Set j) → ... → (a : X Δ τ) → P x a

the case for each constructor is derived like this:
- first, we split the constructor's term into a quantifying telescope Ξ and a return σ, of form X Δ' τs
  (given Δ' ≡ Δ)
- the case is quantified over every argument Ξ of the constructor, and
- for each argument r : X Δ τs ∈ Ξ, the case is quantified over a (x : P τs r)
- for each argument f : Π Δ' → X Δ τs ∈ Ξ, the case is quantified over a (x : Π Δ' → P τs (f Δ'))
- the return value of the case is P τs (con Ξ)
-}

makeInductionPrinciple :: forall m var. TypeCheck var m => Data var -> m (Value var)
makeInductionPrinciple Data{..} =
  do
    let args_quoted = map (second quote) dataArgs
        args_tele :: [Binder Term var]
        args_tele   = map (\(a, b) -> Binder a Visible b) args_quoted

    dataSort <- evaluate (quantify args_tele (quote dataKind))

    motive <- freshWithHint "P"
    the_datum <- freshWithHint "it"

    (ixes, sort) <- getIxTele dataKind
    let datum = appToTele (Con dataName) (args_tele ++ ixes)
        datum :: Elim var

    let motiveSort = quantify ixes $ Pi (Binder the_datum Visible (Elim datum)) (quote sort)
    let motiveT :: Binder Term var
        motiveT = Binder motive Visible motiveSort

    let check = assume dataName dataSort
              . mkCheck (length ixes) (appToTele (Con dataName) args_tele)
    cases <- traverse (makeConCase (length ixes) check motive) dataCons

    evaluate (quantify (map invisCloak args_tele
                     ++ map invisCloak ixes
                     ++ [motiveT]
                     ++ cases
                     ++ [Binder the_datum Visible (Elim datum)])
                (Elim (appToTele (Var motive) (ixes ++ [Binder the_datum Visible (Elim datum)]))))
  where
    getProp motive ixes = foldl App (Var motive) ixes

    -- Build the type for one constructor case.
    -- Arguments:
    --    the count of indices of the data type
    --    a function to checke whether return kinds are correct, and, if so, return the indices for this constructor
    --    the elimination motive, evaluated
    --    the constructor name, and the constructor's kind
    makeConCase ixC checkKind motive (con, kind) = do
      (tele, ret) <- splitPi kind
      let con_appd = appToTele (Con con) (fmap (\b -> b { domain = quote (domain b) }) tele)
          tele' = fmap (\b -> b { domain = quote (domain b)}) tele

      ixes <- checkKind (quote ret)
      inductives <- getInductives ixC tele
        `catchError` \x ->
          case x of
            (NonWellFounded _ x r, l) -> throwError (NonWellFounded con x r, l)
            e -> throwError e
      inductiveArgs <- for inductives $ \(v, ixes, q, thing) -> do
        newv <- refresh v
        pure (Binder newv Visible (q (Elim (App (getProp motive ixes) (Elim thing)))))

      c <- freshWithHint ("case{" ++ show con ++ "}")
      pure (Binder c Visible
              (quantify (tele' ++ inductiveArgs) (Elim (App (getProp motive ixes) (Elim con_appd)))))

    -- Build a checker function for a data type with n indices, with parameters ki
    mkCheck :: Int -> Elim var -> Term var -> m [(Term var)]
    mkCheck len ki (Elim ki') = do
      let (ki'', dropped) = dropArgs ki' len
      t <- evaluate (Elim ki)
      q <- evaluate (Elim ki'')
      _ <- subsumes t q
      -- justification for dropping wrapper: we don't have a term to wrap!
      -- (just checking the types line up, after all.)
      pure (reverse dropped)
    mkCheck _ w h = typeError (WrongDataReturn w h)

    -- Build the induction cases.
    getInductives :: Int -> [Binder Value var] -> m [(var, [Term var], Term var -> Term var, Elim var)]
    getInductives _ [] = pure []

    -- x : Y Ξ τs:
    getInductives ixC (Binder{ var = v, domain = VNe t' }:rst)
      | elimHead t == Con dataName =      -- Y ≡ X. Strictly speaking we should check the indices line up here
          let (_, here_ixes) = dropArgs t ixC
           in ((v, here_ixes, id, Var v):) <$> getInductives ixC rst
      | otherwise = getInductives ixC rst -- ¬(Y ≡ X); This variable doesn't get induced over
      where t = quoteNeutral t'

    -- f : Π Δ', Y Ξ τs
    getInductives ixC (Binder{ var = v, domain = ty@VPi{}}:rst)
      -- Where Y ≡ X,
      -- build an induction hypothesis of the form 
      -- Π Δ', P (f Δ')
      | Elim t <- t, elimHead t == Con dataName = do
        -- if X appears (saturated) in Δ, we should reject it..
        for_ (zip [1..] (fst (splitPi_pure ty))) $ \(i, domain -> t) ->
          case t of
            VNe n | elimHead (quoteNeutral n) == Con dataName ->
              typeError (NonWellFounded (error "empty NonWellFounded variable (getInductives outside of mkConCase?)") i t)
            _ -> pure ()
        let (_, here_ixes) = dropArgs t ixC
          in (( v
              , here_ixes
              , quantify (fmap (\b -> b { domain = quote (domain b) }) tele)
              , appToTele (Var v) tele):)
             <$> getInductives ixC rst

      -- Some other function type. Ignore it
      | otherwise = getInductives ixC rst
      where (tele, ret) = splitPi_pure ty
            t = quote ret

    -- Something else (Set, etc). Just ignore it
    getInductives ixC (_:rst) = getInductives ixC rst

-- | Mark a binder as invisible
invisCloak :: Binder a var -> Binder a var
invisCloak binder = binder { visibility = Invisible }

{-
for a type like

data X Δ : τ → Set j where
  case1 : X Δ τ
  case2 : X Δ τ' → (Y → X Δ τ'') → X Δ τ''

the recursor has the form
induction Δ τ c1 c2 case1       = c1 τ
induction Δ τ c1 c2 (case2 r f) = c2 τ (induction Δ τ c1 c2 r) (λ x → induction Δ τ c1 c2 (f x))
-}
makeRecursor :: forall m var. TypeCheck var m => var -> Data var -> m (Value var)
makeRecursor name Data{..} =
  do
    (tele, _) <- getIxTele dataKind
    let argNames = fst <$> dataArgs
        conNames = fst <$> dataCons
        teleNames = fmap var tele
    motive <- freshWithHint "P"
    value  <- freshWithHint "value"
    let recursor = makeRecursor cases [] (length argNames, length teleNames) (argNames ++ conNames ++ teleNames ++ [motive, value])
        cases    = foldMap (\(i, (var, ty)) -> Map.singleton var (i, goForCase recursor (fst (splitPi_pure ty)))) (zip [0..] dataCons)
    pure recursor
  where
    -- Given:
    -- * A map between constructors and functions which recur on the right arguments
    --     (or build lambdas to recur under, in case of arguments of type Π Δ', X Δ τ)
    -- * An accumulator for values
    -- * A pair containing the number of arguments and indices to the data type we're
    --     eliminating
    -- * A list `arg`, to drive collection of arguments (could be a number, only used for its size)
    -- 
    -- Compute:
    --   A function which accumulates `length arg` arguments, splits on the last of these,
    --   and eliminates the data type X Δ.
    makeRecursor :: Map.Map var (Int, Seq (Value var) -> [Value var] -> Seq (Value var)) -> [Value var] -> (Int, Int) -> [var] -> Value var
    makeRecursor cases acc (nArgs, nIndices) [] =
      case acc of
        head:_ | Just ((i, worker), cArgs) <- isCon cases head ->
          foldl (@@) (args !! (skip + i)) (cArgs <> worker cArgs static)
        _ -> (foldl (@@) (valueVar name) (reverse acc))
      where
        args = reverse acc
        skip = nArgs + nIndices + 1
        static = take (1 + nIndices + length cases) (drop nArgs args)
    makeRecursor cases acc skip (n:rest) = VFn n (\v -> makeRecursor cases (v:acc) skip rest)

    -- Is the given value a neutral application of a constructor of this data type?
    isCon :: Map.Map var (Int, Seq (Value var) -> [Value var] -> Seq (Value var))
          -> Value var
          -> Maybe ((Int, Seq (Value var) -> [Value var] -> Seq (Value var)), Seq (Value var))
    isCon cases (VNe (NApp (NCon x) args)) = flip (,) args <$> Map.lookup x cases
    isCon cases (VNe (NCon x)) = flip (,) mempty <$> Map.lookup x cases
    isCon _ _ = Nothing

    -- Build the individual eliminator for each case, given:
    --   * a reference to the recursor (yay, knot-tying!)
    --   * A telescope of this constructor's arguments
    --
    -- Compute a function that, given:
    --   * The arguments passed to this constructor, and
    --   * The arguments that do not change (indices)
    --
    -- Computes: The arguments to this data type, with recursive
    -- occurences eliminated (even under lambda).
    goForCase :: Value var -> [Binder Value var] -> Seq (Value var) -> [Value var] -> Seq (Value var)
    goForCase _ []  _ _                         = mempty

    -- a : Y Δ' τ
    goForCase recursor ((domain -> VNe t'):rst) (arg Seq.:<| args) extraArgs
      | elimHead (quoteNeutral t') == Con dataName
      -- Y ≡ X, recur
      = (foldl (@@) recursor extraArgs) @@ arg Seq.:<| goForCase recursor rst args extraArgs
      -- ← (Y ≡ X), ignore
      | otherwise = goForCase recursor rst args extraArgs

    -- f : Π Ξ, Y Δ' τ
    goForCase recursor ((domain -> ty@VPi{}):rst) (argf Seq.:<| args) extraArgs
      -- Y ≡ X, build λ Ξ → recursor (f Ξ) (i.e., recursor . f, but polymorphic over a telescope)
      | Elim t <- t, elimHead t == Con dataName =
         makeFun recursor (fst (splitPi_pure ty)) argf Seq.:<| goForCase recursor rst args extraArgs
      -- ¬ (Y ≡ X), pass along
      | otherwise = goForCase recursor rst args extraArgs
      where (_, ret) = splitPi_pure ty
            t = quote ret

    -- Different thing (Set, etc), just pass it along
    goForCase recursor (_:rst) (_ Seq.:<| args) extraArgs = goForCase recursor rst args extraArgs

    -- This case is impossible
    goForCase _ _ _ _ = error "Type error in recursor"

-- Given recursor, Ξ and f, build λ Ξ → recursor (f Ξ)
makeFun :: (Show var, Eq var) => Value var -> [Binder Value var] -> Value var -> Value var
makeFun recursor []  x         = recursor @@ x
makeFun recursor (Binder {var = n}:xs) f = VFn n $ \a -> makeFun recursor xs (f @@ a)

getIxTele :: TypeCheck var m => Value var -> m ([Binder Term var], Value var)
getIxTele kind = do
  (tele, i) <- splitPi kind
  let l = fmap (\b -> b { domain = quote (domain b) }) tele
  case i of
    VSet -> pure (l, VSet)
    VProp -> pure (l, VProp)
    _ -> typeError (InvalidDataKind i)

splitPi' :: Monad m => (var -> m var) -> Value var -> m ([Binder Value var], Value var)
splitPi' rename (VPi binder rest) = do
  v' <- rename (var binder)
  first (binder { var = v' }:) <$> splitPi' rename (rest (valueVar v'))
splitPi' _ t = pure ([], t)

splitPi :: TypeCheck var m => Value var -> m ([Binder Value var], Value var)
splitPi = splitPi' refresh

splitPi_pure :: Value var -> ([Binder Value var], Value var)
splitPi_pure = runIdentity . splitPi' pure

appToTele :: Elim var -> [Binder a var] -> Elim var
appToTele x [] = x
appToTele x (binder:xs) = appToTele (App x (Elim (Var (var binder)))) xs

dropArgs :: Elim var -> Int -> (Elim var, [Term var])
dropArgs x 0 = (x, [])
dropArgs (App f t) n = second (t:) $ dropArgs f (n - 1)
dropArgs x@Var{} _ = (x, [])
dropArgs x@Con{} _ = (x, [])
dropArgs x@Meta{} _ = (x, [])
dropArgs x@Cut{} _ = (x, [])

elimHead :: Elim var -> Elim var
elimHead (App f _) = elimHead f
elimHead x = x