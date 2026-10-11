-- A proof-obligation layer over the canonical executable learner.
-- C.Int8 is an unbounded integer wrapper (C.Int = ℤ), not bounded 8-bit
-- arithmetic.  No descent proof is postulated or claimed by this module.
{-# OPTIONS
  --without-K
  --level-universe
#-}

module FullCoupled.LearnerLogicalSpec where

open import MLTT.Spartan hiding (J; _+_)
open import Integers.Type
open import Naturals.Addition
open import Naturals.Order
import Naturals.Multiplication as NatMult
import FullCoupled.CanonicalLearnerMonolith as C

infixl 32 _ℕ*_
_ℕ*_ : ℕ → ℕ → ℕ
_ℕ*_ = NatMult._*_

integerMagnitude : C.Int → ℕ
integerMagnitude (pos n) = n
integerMagnitude (negsucc n) = succ n

int8DifferenceMagnitude : C.Int8 → C.Int8 → ℕ
int8DifferenceMagnitude x y =
  integerMagnitude (C.code (C.int8Sub x y))

squareNat : ℕ → ℕ
squareNat n = n ℕ* n

sumFive : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
sumFive a b c d e = (((a + b) + c) + d) + e

optimizerOrigin : C.F4IntUState
optimizerOrigin =
  C.f4IntUState C.zero8 C.zero8 C.zero8 C.zero8 C.zero8

-- Exact ℤ-coordinate distance over the five canonical optimizer channels.
optimizerDistance : C.F4IntUState → C.F4IntUState → ℕ
optimizerDistance s t =
  sumFive
    (squareNat (int8DifferenceMagnitude (C.thetaQ s) (C.thetaQ t)))
    (squareNat (int8DifferenceMagnitude (C.rTheta s) (C.rTheta t)))
    (squareNat (int8DifferenceMagnitude (C.eQ s) (C.eQ t)))
    (squareNat (int8DifferenceMagnitude (C.rE s) (C.rE t)))
    (squareNat (int8DifferenceMagnitude (C.rL s) (C.rL t)))

-- A natural-valued quadratic candidate; non-negativity follows from its type.
optimizerQuadratic : C.F4IntUState → ℕ
optimizerQuadratic s = optimizerDistance s optimizerOrigin

-- The raw one-step descent obligation for the actual f4ThetaStep transition.
-- This is a proposition only: deliberately no inhabitant is supplied.
f4ThetaOneStepDescentObligation :
  (K : C.F4IntUKernel)
  (s : C.F4IntUState)
  (signal : C.Int8) →
  optimizerQuadratic (C.f4ThetaStep K s signal) <ℕ optimizerQuadratic s
f4ThetaOneStepDescentObligation K s signal =
  optimizerQuadratic (C.f4ThetaStep K s signal) <ℕ optimizerQuadratic s

-- Same obligation at the canonical full-learner boundary.
canonicalOptimizerDescentObligation :
  ∀ {A : Set}
    (K : C.FullLearnerKernel A)
    (s : C.FullLearnerState A) →
  optimizerQuadratic (C.canonicalOptimizerStep K s) <ℕ
  optimizerQuadratic (C.optimizer s)
canonicalOptimizerDescentObligation K s =
  optimizerQuadratic (C.canonicalOptimizerStep K s) <ℕ
  optimizerQuadratic (C.optimizer s)

canonicalOptimizerStepMatchesThetaStep :
  ∀ {A : Set}
    (K : C.FullLearnerKernel A)
    (s : C.FullLearnerState A) →
  C.canonicalOptimizerStep K s ＝
  C.f4ThetaStep
    (C.optimizerKernel K)
    (C.optimizer s)
    (C.canonicalWatkinsTarget K s)
canonicalOptimizerStepMatchesThetaStep =
  C.canonicalOptimizerStep-qMunchausen-L2

-- A certificate is conditional on an explicit admissible-state predicate.
-- No certificate value is manufactured: strict descent and preservation are
-- the proof obligations a later mathematical argument must discharge.
record LearnerDescentCertificate
  {A : Set}
  (K : C.FullLearnerKernel A)
  (admissible : C.FullLearnerState A → Set) : Set₁ where
  constructor learnerDescentCertificate
  field
    strictDescentUnderAdmissibility :
      ∀ s → admissible s →
        canonicalOptimizerDescentObligation K s
    admissibilityPreserved :
      ∀ s → admissible s →
        admissible (C.canonicalFullStep K s)

-- A ℕ-indexed trace makes initiality and every guarded step explicit.
record GuardedLearnerTrace
  {A : Set}
  (K : C.FullLearnerKernel A)
  (initial : C.FullLearnerState A) : Set₁ where
  constructor guardedLearnerTrace
  field
    traceState : ℕ → C.FullLearnerState A
    traceStartsAtInitial : traceState zero ＝ initial
    traceStep : ∀ n →
      traceState (succ n) ＝ C.canonicalFullStep K (traceState n)

open GuardedLearnerTrace public

canonicalLearnerTrace :
  ∀ {A : Set}
    (K : C.FullLearnerKernel A)
    (initial : C.FullLearnerState A) →
  ℕ → C.FullLearnerState A
canonicalLearnerTrace K initial zero = initial
canonicalLearnerTrace K initial (succ n) =
  C.canonicalFullStep K (canonicalLearnerTrace K initial n)

canonicalLearnerTraceGuarded :
  ∀ {A : Set}
    (K : C.FullLearnerKernel A)
    (initial : C.FullLearnerState A) →
  GuardedLearnerTrace K initial
canonicalLearnerTraceGuarded K initial =
  guardedLearnerTrace
    (canonicalLearnerTrace K initial)
    refl
    (λ n → refl)
