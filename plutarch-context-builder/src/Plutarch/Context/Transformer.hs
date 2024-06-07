{-# OPTIONS_GHC -Wno-orphans #-}

module Plutarch.Context.Transformer (
  -- * Data type
  Transformer,
  -- * Introduction
  -- ** Generic
  liftDatumEndo,
  liftDatumKleisli,
  liftDatumCheck,
  liftRedeemerEndo,
  liftRedeemerKleisli,
  liftRedeemerCheck,
  liftScriptContextEndo,
  liftScriptContextKleisli,
  liftScriptContextCheck,
  liftValidatorEndo,
  liftValidatorKleisli,
  liftValidatorCheck,
  liftMintingPolicyEndo,
  liftMintingPolicyKleisli,
  liftMintingPolicyCheck,
  -- ** Specific checkers
  txInfoRedeemersAreSorted,
  txInfoOutputsAreSorted,
  -- ** Specific normalizers
  sortTxInfoRedeemers,
  sortTxInfoOutputs,
  -- * Elimination
  runValidatorTransformer,
  runValidatorTransformerPure,
  runMintingPolicyTransformer,
  runMintingPolicyTransformerPure
  ) where

import Control.Applicative ((<|>))
import Data.Void (Void, absurd)
import Control.Monad.Except (MonadError (throwError))
import Data.Bifunctor (first)
import Control.Arrow (Kleisli (Kleisli))
import Data.Kind (Type)
import Control.Category ((>>>), id)
import Prelude hiding (id)
import Data.Profunctor (Star (Star))
import PlutusLedgerApi.V2 (ScriptContext (scriptContextTxInfo), 
  txInfoRedeemers, ScriptPurpose (Minting, Spending, Rewarding, Certifying), 
  txInfoOutputs, txOutReferenceScript)
import Data.Profunctor.Rep (tabulate)
import Data.Monoid (Endo (Endo, appEndo))
import PlutusTx.AssocMap qualified as AssocMap
import Data.List (sort, sortOn)

-- | @since 3.0.1
newtype Transformer (d :: Type) (r :: Type) (err :: Type) = 
  Transformer (Star (Either err) (Maybe d, r, ScriptContext) (Maybe d, r, ScriptContext))

-- | Verifies that 'txInfoRedeemers' in a 'ScriptContext' are sorted.
--
-- @since 3.0.1
txInfoRedeemersAreSorted :: forall (d :: Type) (r :: Type) (err :: Type) . 
  -- | Error to produce on failure
  err -> 
  Transformer d r err
txInfoRedeemersAreSorted onFailure = liftScriptContextCheck . Kleisli $ \sc -> do
  let tirs = AssocMap.toList . txInfoRedeemers . scriptContextTxInfo $ sc
  if isSorted tirs
    then Nothing
    else Just onFailure

-- | Verifies that 'txInfoOutputs' are sorted on reference scripts.
--
-- @since 3.0.1
txInfoOutputsAreSorted :: forall (d :: Type) (r :: Type) (err :: Type) . 
  -- | Error to produce on failure
  err -> 
  Transformer d r err
txInfoOutputsAreSorted onFailure = liftScriptContextCheck . Kleisli $ \sc -> do
  let tios = txInfoOutputs . scriptContextTxInfo $ sc
  if isSortedBy txOutReferenceScript tios
    then Nothing
    else Just onFailure

-- | Ensures that the 'txInfoRedeemers' in a 'ScriptContext' are sorted.
--
-- @since 3.0.1
sortTxInfoRedeemers :: forall (d :: Type) (r :: Type) (err :: Type) . 
  Transformer d r err
sortTxInfoRedeemers = liftScriptContextEndo . Endo $ \sc -> 
  let tinfo = scriptContextTxInfo sc
      tirs = AssocMap.toList . txInfoRedeemers $ tinfo
      tirs' = AssocMap.fromList . sort $ tirs
    in sc { scriptContextTxInfo = tinfo { txInfoRedeemers = tirs' } }

-- | Ensures that the 'txInfoOutputs' are sorted on reference scripts.
--
-- @since 3.0.1
sortTxInfoOutputs :: forall (d :: Type) (r :: Type) (err :: Type) . 
  Transformer d r err
sortTxInfoOutputs = liftScriptContextEndo . Endo $ \sc -> 
  let tinfo = scriptContextTxInfo sc
      tios = txInfoOutputs tinfo
      tios' = sortOn txOutReferenceScript tios
    in sc { scriptContextTxInfo = tinfo { txInfoOutputs = tios' } }

-- | Given a 'Transformer' for a validator, produce a 'Kleisli' for validator
-- arguments based on it in an arbitrary 'MonadError'.
--
-- @since 3.0.1
runValidatorTransformer :: forall (d :: Type) (r :: Type) (err :: Type) (m :: Type -> Type) . 
  MonadError err m => 
  Transformer d r err -> 
  Kleisli m (d, r, ScriptContext) (d, r, ScriptContext)
runValidatorTransformer (Transformer (Star f)) = Kleisli $ \(d, r, sc) -> 
  case f (Just d, r, sc) of 
    Left err -> throwError err
    Right (md', r', sc') -> pure $ case md' of 
      Nothing -> (d, r', sc') -- technically impossible
      Just d' -> (d', r', sc')

-- | As 'runValidatorTransformer', but knowing that we cannot error allows us to
-- produce an 'Endo' instead.
--
-- @since 3.0.1
runValidatorTransformerPure :: forall (d :: Type) (r :: Type) . 
  Transformer d r Void -> 
  Endo (d, r, ScriptContext)
runValidatorTransformerPure (Transformer (Star f)) = Endo $ \(d, r, sc) -> 
  case f (Just d, r, sc) of 
    -- Since Either Void ~ Identity, if we ever get a Left, we've left the realm
    -- of possibility.
    Left impossible -> absurd impossible
    Right (md', r', sc') -> case md' of 
      Nothing -> (d, r', sc') -- technically impossible
      Just d' -> (d', r', sc') 

-- | Given a 'Transformer' ignorant of datums, produce a 'Kleisli' for minting
-- policy arguments based on it in an arbitrary 'MonadError'.
--
-- @since 3.0.1
runMintingPolicyTransformer :: forall (r :: Type) (err :: Type) (m :: Type -> Type) . 
  MonadError err m => 
  Transformer Void r err -> 
  Kleisli m (r, ScriptContext) (r, ScriptContext)
runMintingPolicyTransformer (Transformer (Star f)) = Kleisli $ \(r, sc) -> 
  case f (Nothing, r, sc) of 
    Left err -> throwError err
    -- This works because Maybe Void ~ (), so thus, it never matters what the
    -- 'datum' result actually is.
    Right (_, r', sc') -> pure (r', sc')

-- | As 'runMintingPolicyTransformer', but knowing that we cannot error allows
-- us to produce an 'Endo' instead.
--
-- @since 3.0.1
runMintingPolicyTransformerPure :: forall (r :: Type) . 
  Transformer Void r Void -> 
  Endo (r, ScriptContext)
runMintingPolicyTransformerPure (Transformer (Star f)) = Endo $ \(r, sc) -> 
  case f (Nothing, r, sc) of 
    Left impossible -> absurd impossible
    Right (_, r', sc') -> (r', sc')

-- | Transforms the error type.
--
-- @since 3.0.1
instance Functor (Transformer d r) where
  {-# INLINEABLE fmap #-}
  fmap f (Transformer (Star g)) = Transformer . Star $ first f . g

-- | @since 3.0.1
instance Semigroup (Transformer d r err) where
  {-# INLINEABLE (<>) #-}
  Transformer f <> Transformer g = Transformer $ f >>> g

-- | @since 3.0.1
instance Monoid (Transformer d r err) where
  {-# INLINEABLE mempty #-}
  mempty = Transformer id

-- | Lift an 'Endo' on the datum argument into a 'Transformer'.
--
-- @since 3.0.1
liftDatumEndo :: forall (d :: Type) (r :: Type) (err :: Type) .
  Endo d -> Transformer d r err
liftDatumEndo f = liftEndo . Endo $ \(x, y, sc) -> (appEndo f <$> x, y, sc)

-- | Lift a 'Kleisli' on the datum argument into a 'Transformer'.
--
-- @since 3.0.1
liftDatumKleisli :: forall (d :: Type) (r :: Type) (err :: Type) . 
  Kleisli (Either err) d d -> 
  Transformer d r err
liftDatumKleisli (Kleisli f) = liftKleisli . Kleisli $ \(md, r, sc) -> case traverse f md of 
  Left err -> Left err
  Right md' -> Right (md', r, sc)

-- | Given a function possibly producing an error from a datum, generate 
-- a \'checker\' 'Transformer' that passes through its arguments if the 
-- function gives 'Nothing', and errors as specified otherwise.
--
-- @since 3.0.1
liftDatumCheck :: forall (d :: Type) (r :: Type) (err :: Type) . 
  Kleisli Maybe d err -> 
  Transformer d r err
liftDatumCheck (Kleisli f) = liftCheck . Kleisli $ \(md, _, _) ->
  case traverse f md of
    -- This one is a bit of a brain twister due to the double-up of Maybe.
    -- Essentially, there are three possibilities:
    --
    -- * Nothing (no datum to check) -> vacuous pass
    -- * Just Nothing (datum to check, but no error found) -> pass
    -- * Just (Just err) (datum to check, error found) -> forward error
    Just (Just err) -> Just err
    _ -> Nothing

-- | Lift an 'Endo' on the redeemer argument into a 'Transformer'.
--
-- @since 3.0.1
liftRedeemerEndo :: forall (d :: Type) (r :: Type) (err :: Type) .
  Endo r -> Transformer d r err
liftRedeemerEndo f = liftEndo . Endo $ \(x, y, sc) -> (x, appEndo f y, sc)

-- | Lift a 'Kleisli' on the redeemer argument into a 'Transformer'.
--
-- @since 3.0.1
liftRedeemerKleisli :: forall (d :: Type) (r :: Type) (err :: Type) . 
  Kleisli (Either err) r r -> 
  Transformer d r err
liftRedeemerKleisli (Kleisli f) = liftKleisli . Kleisli $ \(md, r, sc) -> case f r of 
  Left err -> Left err
  Right r' -> Right (md, r', sc)

-- | Given a function possibly producing an error from a redeemer, generate 
-- a \'checker\' 'Transformer' that passes through its arguments if the 
-- function gives 'Nothing', and errors as specified otherwise.
--
-- @since 3.0.1
liftRedeemerCheck :: forall (d :: Type) (r :: Type) (err :: Type) . 
  Kleisli Maybe r err -> 
  Transformer d r err
liftRedeemerCheck (Kleisli f) = liftCheck . Kleisli $ \(_, r, _) ->
  f r <|> Nothing

-- | Lift an 'Endo' on 'ScriptContext's into a 'Transformer'.
--
-- @since 3.0.1
liftScriptContextEndo :: forall (d :: Type) (r :: Type) (err :: Type) . 
  Endo ScriptContext -> Transformer d r err
liftScriptContextEndo f = liftEndo . Endo $ \(x, y, sc) -> (x, y, appEndo f sc)

-- | Lift a 'Kleisli' on 'ScriptContext's into a 'Transformer'.
--
-- @since 3.0.1
liftScriptContextKleisli :: forall (d :: Type) (r :: Type) (err :: Type) . 
  Kleisli (Either err) ScriptContext ScriptContext -> 
  Transformer d r err
liftScriptContextKleisli (Kleisli f) = liftKleisli . Kleisli $ \(md, r, sc) -> case f sc of 
  Left err -> Left err
  Right sc' -> Right (md, r, sc')

-- | Given a function possibly producing an error from a 'ScriptContext', generate 
-- a \'checker\' 'Transformer' that passes through its arguments if the 
-- function gives 'Nothing', and errors as specified otherwise.
--
-- @since 3.0.1
liftScriptContextCheck :: forall (d :: Type) (r :: Type) (err :: Type) . 
  Kleisli Maybe ScriptContext err -> 
  Transformer d r err
liftScriptContextCheck (Kleisli f) = liftCheck . Kleisli $ \(_, _, sc) ->
  f sc <|> Nothing

-- | Lift an 'Endo' on all validator arguments into a 'Transformer'.
--
-- @since 3.0.1
liftValidatorEndo :: forall (d :: Type) (r :: Type) (err :: Type) . 
  Endo (d, r, ScriptContext) -> 
  Transformer d r err
liftValidatorEndo f = liftEndo . Endo $ \(md, r, sc) -> case md of 
  Nothing -> (Nothing, r, sc)
  Just d -> let (d', r', sc') = appEndo f (d, r, sc) in 
    (Just d', r', sc')

-- | Lift a 'Kleisli' on all validator arguments into a 'Transformer'.
--
-- @since 3.0.1
liftValidatorKleisli :: forall (d :: Type) (r :: Type) (err :: Type) . 
  Kleisli (Either err) (d, r, ScriptContext) (d, r, ScriptContext) -> 
  Transformer d r err
liftValidatorKleisli (Kleisli f) = liftKleisli . Kleisli $ \(md, r, sc) -> 
  case md of 
    Nothing -> Right (Nothing, r, sc)
    Just d -> fmap (\(d', r', sc') -> (Just d', r', sc')) <$> f $ (d, r, sc)

-- | Given a function possibly producing an error from validator arguments, 
-- generate a \'checker\' 'Transformer' that passes through its arguments if 
-- the function gives 'Nothing', and errors as specified otherwise.
--
-- @since 3.0.1
liftValidatorCheck :: forall (d :: Type) (r :: Type) (err :: Type) . 
  Kleisli Maybe (d, r, ScriptContext) err -> 
  Transformer d r err
liftValidatorCheck (Kleisli f) = liftCheck . Kleisli $ \(md, r, sc) -> 
  md >>= \d -> f (d, r, sc) >>= Just

-- | Lift an 'Endo' on all minting policy arguments into a 'Transformer'.
--
-- @since 3.0.1
liftMintingPolicyEndo :: forall (d :: Type) (r :: Type) (err :: Type) . 
  Endo (r, ScriptContext) -> 
  Transformer d r err
liftMintingPolicyEndo f = liftEndo . Endo $ \(md, r, sc) -> 
  let (r', sc') = appEndo f (r, sc) in 
    (md, r', sc')

-- | Lift a 'Kleisli' on all minting policy arguments into a 'Transformer'.
--
-- @since 3.0.1
liftMintingPolicyKleisli :: forall (d :: Type) (r :: Type) (err :: Type) . 
  Kleisli (Either err) (r, ScriptContext) (r, ScriptContext) -> 
  Transformer d r err
liftMintingPolicyKleisli (Kleisli f) = liftKleisli . Kleisli $ \(md, r, sc) -> 
  f (r, sc) >>= \(r', sc') -> pure (md, r', sc')

-- | Given a function possibly producing an error from minting policy arguments, 
-- generate a \'checker\' 'Transformer' that passes through its arguments if 
-- the function gives 'Nothing', and errors as specified otherwise.
--
-- @since 3.0.1
liftMintingPolicyCheck :: forall (d :: Type) (r :: Type) (err :: Type) . 
  Kleisli Maybe (r, ScriptContext) err -> 
  Transformer d r err
liftMintingPolicyCheck (Kleisli f) = liftCheck . Kleisli $ \(_, r, sc) -> 
  f (r, sc) >>= Just 

-- Helpers

liftEndo :: forall (d :: Type) (r :: Type) (err :: Type) . 
  Endo (Maybe d, r, ScriptContext) -> 
  Transformer d r err
liftEndo f = Transformer . tabulate $ pure . appEndo f

liftKleisli :: forall (d :: Type) (r :: Type) (err :: Type) .
  Kleisli (Either err) (Maybe d, r, ScriptContext) (Maybe d, r, ScriptContext) -> 
  Transformer d r err
liftKleisli (Kleisli arr) = Transformer . tabulate $ arr

liftCheck :: forall (d :: Type) (r :: Type) (err :: Type) . 
  Kleisli Maybe (Maybe d, r, ScriptContext) err -> 
  Transformer d r err
liftCheck (Kleisli f) = Transformer . tabulate $ \(md, r, sc) -> case f (md, r, sc) of 
  Nothing -> pure (md, r, sc)
  Just err -> Left err

isSorted :: forall (a :: Type) . 
  Ord a => 
  [a] -> Bool
isSorted = isSortedBy id

isSortedBy :: forall (a :: Type) (b :: Type) . 
  Ord b => 
  (a -> b) -> 
  [a] -> 
  Bool
isSortedBy f = \case
  [] -> True
  (x : xs) -> go (f x) xs
  where
    go :: b -> [a] -> Bool
    go x = \case
      [] -> True
      (y : ys) -> let y' = f y in
        (x <= y') && go y' ys

-- Temporary solution for the problem of comparison
deriving stock instance Ord ScriptPurpose
