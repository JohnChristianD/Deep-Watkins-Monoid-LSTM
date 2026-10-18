{-# OPTIONS --erased-matches #-}

------------------------------------------------------------------------
-- Exact finite-state/action tabular Q approximation.
--
-- This is a deliberately small, sound baseline for the discrete scenario.
-- Parameters are lookup tables, so every Q-function on Fin stateCount ×
-- Fin actionCount is represented exactly. Consequently it satisfies a
-- pointwise-uniform epsilon approximation contract for every admissible
-- tolerance, without assuming that a recurrent/LSTM architecture is dense.
--
-- Do not confuse this finite tabular theorem with a classical UAP theorem
-- for a fixed neural architecture on a compact real domain. That theorem
-- needs a concrete architecture, activation, topology/norm, target class,
-- and a proof of density. This file proves the finite-domain exact case.
------------------------------------------------------------------------

module FullCoupled.FiniteTabularUAP where

open import Haskell.Prelude using (Nat; zero; suc; _≡_)
open import FullCoupled.ReflectionAutomation using (byDefinitionalRefl)

data Fin : Nat → Set where
  fzero : {n : Nat} → Fin (suc n)
  fsuc  : {n : Nat} → Fin n → Fin (suc n)

-- The evaluator's parameter space is precisely the finite table of
-- state/action values.
TabularParameters :
  (stateCount actionCount : Nat) → (Scalar : Set) → Set
TabularParameters stateCount actionCount Scalar =
  Fin stateCount → Fin actionCount → Scalar

tabularQ :
  {stateCount actionCount : Nat} {Scalar : Set} →
  TabularParameters stateCount actionCount Scalar →
  Fin stateCount → Fin actionCount → Scalar
tabularQ parameters = parameters

tabularParameterize :
  {stateCount actionCount : Nat} {Scalar : Set} →
  (Fin stateCount → Fin actionCount → Scalar) →
  TabularParameters stateCount actionCount Scalar
tabularParameterize target = target

-- Exact readout, proved by computation rather than postulated.
tabularQExact :
  {stateCount actionCount : Nat} {Scalar : Set} →
  (target : TabularParameters stateCount actionCount Scalar) →
  (state : Fin stateCount) → (action : Fin actionCount) →
  tabularQ (tabularParameterize target) state action ≡ target state action
tabularQExact target state action = byDefinitionalRefl

-- Epsilon ranges over admissible tolerances. exactWithin expresses the
-- metric/order fact that zero error is within any such tolerance; e.g.
-- distance x x ≤ epsilon when epsilon is known nonnegative.
record ApproximationRelation (Scalar Tolerance : Set) : Set₁ where
  field
    Within : Scalar → Scalar → Tolerance → Set
    exactWithin :
      (value : Scalar) → (epsilon : Tolerance) →
      Within value value epsilon

open ApproximationRelation public

record FiniteTabularApproximationWitness
  {stateCount actionCount : Nat}
  {Scalar Tolerance : Set}
  (relation : ApproximationRelation Scalar Tolerance)
  (target : TabularParameters stateCount actionCount Scalar)
  (epsilon : Tolerance) : Set where
  constructor finiteTabularApproximationWitness
  field
    witnessParameters : TabularParameters stateCount actionCount Scalar
    witnessUniformError :
      (state : Fin stateCount) → (action : Fin actionCount) →
      Within relation
        (target state action)
        (tabularQ witnessParameters state action)
        epsilon

-- Finite-domain exact UAP: for every target table and every admissible
-- epsilon, there is one parameter table whose output is within epsilon of
-- the target at every state/action pair. Choose the target table itself.
finiteTabularUniformApproximation :
  {stateCount actionCount : Nat}
  {Scalar Tolerance : Set} →
  (relation : ApproximationRelation Scalar Tolerance) →
  (target : TabularParameters stateCount actionCount Scalar) →
  (epsilon : Tolerance) →
  FiniteTabularApproximationWitness relation target epsilon
finiteTabularUniformApproximation relation target epsilon =
  finiteTabularApproximationWitness
    target
    (λ state action → exactWithin relation (target state action) epsilon)
