{-# OPTIONS --safe #-}

module FullCoupled.EfficientCHADRNN where

-- Haskell-facing recurrent IR. Local JVP/VJP functions are first-class
-- representation data; proof evidence is erased from extracted Haskell.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; _+_)

record RNNStep (A T C : Set) : Set where
  constructor rnnStep
  field
    stepPrimal : A → A
    stepJVP    : A → T → T
    stepVJP    : A → C → C
    stepCost   : Nat

open RNNStep public
{-# COMPILE AGDA2HS RNNStep #-}

identityStep : {A T C : Set} → RNNStep A T C
identityStep =
  record
    { stepPrimal = λ x → x
    ; stepJVP    = λ x dx → dx
    ; stepVJP    = λ x dc → dc
    ; stepCost   = zero
    }
{-# COMPILE AGDA2HS identityStep #-}

-- composeStep f g means: run f first, then g.
composeStep : {A T C : Set} → RNNStep A T C → RNNStep A T C → RNNStep A T C
composeStep f g =
  record
    { stepPrimal = λ x → stepPrimal g (stepPrimal f x)
    ; stepJVP    = λ x dx →
        stepJVP g (stepPrimal f x) (stepJVP f x dx)
    ; stepVJP    = λ x dc →
        stepVJP f x (stepVJP g (stepPrimal f x) dc)
    ; stepCost   = stepCost f + stepCost g
    }
{-# COMPILE AGDA2HS composeStep #-}

compileSteps : {A T C : Set} → List (RNNStep A T C) → RNNStep A T C
compileSteps [] = identityStep
compileSteps (s ∷ ss) = composeStep s (compileSteps ss)
{-# COMPILE AGDA2HS compileSteps #-}

runSteps : {A T C : Set} → List (RNNStep A T C) → A → A
runSteps [] x = x
runSteps (s ∷ ss) x = runSteps ss (stepPrimal s x)
{-# COMPILE AGDA2HS runSteps #-}

pushSteps : {A T C : Set} → List (RNNStep A T C) → A → T → T
pushSteps [] x dx = dx
pushSteps (s ∷ ss) x dx =
  pushSteps ss (stepPrimal s x) (stepJVP s x dx)
{-# COMPILE AGDA2HS pushSteps #-}

pullSteps : {A T C : Set} → List (RNNStep A T C) → A → C → C
pullSteps [] x dc = dc
pullSteps (s ∷ ss) x dc =
  stepVJP s x (pullSteps ss (stepPrimal s x) dc)
{-# COMPILE AGDA2HS pullSteps #-}

workSteps : {A T C : Set} → List (RNNStep A T C) → Nat
workSteps [] = zero
workSteps (s ∷ ss) = stepCost s + workSteps ss
{-# COMPILE AGDA2HS workSteps #-}

------------------------------------------------------------------------
-- Correctness of compiling a recurrent list into one composed step
------------------------------------------------------------------------

primalSimulation :
  {A T C : Set} →
  (ss : List (RNNStep A T C)) →
  (x : A) →
  runSteps ss x ≡ stepPrimal (compileSteps ss) x
primalSimulation [] x = refl
primalSimulation (s ∷ ss) x = refl

pushSimulation :
  {A T C : Set} →
  (ss : List (RNNStep A T C)) →
  (x : A) →
  (dx : T) →
  pushSteps ss x dx ≡ stepJVP (compileSteps ss) x dx
pushSimulation [] x dx = refl
pushSimulation (s ∷ ss) x dx = refl

pullSimulation :
  {A T C : Set} →
  (ss : List (RNNStep A T C)) →
  (x : A) →
  (dc : C) →
  pullSteps ss x dc ≡ stepVJP (compileSteps ss) x dc
pullSimulation [] x dc = refl
pullSimulation (s ∷ ss) x dc = refl

workSimulation :
  {A T C : Set} →
  (ss : List (RNNStep A T C)) →
  stepCost (compileSteps ss) ≡ workSteps ss
workSimulation [] = refl
workSimulation (s ∷ ss) = refl

record RNNCompilerSimulation {A T C : Set}
  (ss : List (RNNStep A T C)) : Set where
  field
    primalAgrees : (x : A) →
      runSteps ss x ≡ stepPrimal (compileSteps ss) x
    tangentAgrees : (x : A) → (dx : T) →
      pushSteps ss x dx ≡ stepJVP (compileSteps ss) x dx
    cotangentAgrees : (x : A) → (dc : C) →
      pullSteps ss x dc ≡ stepVJP (compileSteps ss) x dc
    workAgrees :
      stepCost (compileSteps ss) ≡ workSteps ss

rnnCompilerSimulation :
  {A T C : Set} →
  (ss : List (RNNStep A T C)) →
  RNNCompilerSimulation ss
rnnCompilerSimulation ss =
  record
    { primalAgrees    = primalSimulation ss
    ; tangentAgrees   = pushSimulation ss
    ; cotangentAgrees = pullSimulation ss
    ; workAgrees      = workSimulation ss
    }

------------------------------------------------------------------------
-- Local adjoint laws compose into a global reverse-mode correctness law
------------------------------------------------------------------------

trans :
  {A : Set} {x y z : A} →
  x ≡ y → y ≡ z → x ≡ z
trans refl q = q

AdjointLaw :
  {A T C R : Set} →
  (T → C → R) →
  RNNStep A T C →
  Set
AdjointLaw {A} {T} {C} {R} pairing s =
  (x : A) → (dx : T) → (dc : C) →
  pairing (stepJVP s x dx) dc ≡
  pairing dx (stepVJP s x dc)

composeAdjoint :
  {A T C R : Set} →
  (pairing : T → C → R) →
  (f g : RNNStep A T C) →
  AdjointLaw pairing f →
  AdjointLaw pairing g →
  AdjointLaw pairing (composeStep f g)
composeAdjoint pairing f g fLaw gLaw x dx dc =
  trans
    (gLaw (stepPrimal f x) (stepJVP f x dx) dc)
    (fLaw x dx (stepVJP g (stepPrimal f x) dc))

data AllAdjoints {A T C R : Set}
  (pairing : T → C → R) :
  List (RNNStep A T C) → Set where
  noAdjoints :
    AllAdjoints pairing []
  consAdjoint :
    {s : RNNStep A T C} →
    {ss : List (RNNStep A T C)} →
    AdjointLaw pairing s →
    AllAdjoints pairing ss →
    AllAdjoints pairing (s ∷ ss)

compiledAdjoint :
  {A T C R : Set} →
  (pairing : T → C → R) →
  {ss : List (RNNStep A T C)} →
  AllAdjoints pairing ss →
  AdjointLaw pairing (compileSteps ss)
compiledAdjoint pairing noAdjoints x dx dc = refl
compiledAdjoint pairing (consAdjoint {s = s} {ss = ss} local rest) =
  composeAdjoint pairing s (compileSteps ss)
    local (compiledAdjoint pairing rest)

------------------------------------------------------------------------
-- Proof-carrying Möbius RNN package
------------------------------------------------------------------------

record MobiusRNN (A T C R : Set) : Set where
  field
    rnnPairing : T → C → R
    rnnSteps   : List (RNNStep A T C)
    @0 rnnAdjoints : AllAdjoints rnnPairing rnnSteps

open MobiusRNN public
{-# COMPILE AGDA2HS MobiusRNN #-}

compileMobiusRNN :
  {A T C R : Set} →
  MobiusRNN A T C R →
  RNNStep A T C
compileMobiusRNN net = compileSteps (rnnSteps net)
{-# COMPILE AGDA2HS compileMobiusRNN #-}

mobiusRNNCompilerSimulation :
  {A T C R : Set} →
  (net : MobiusRNN A T C R) →
  RNNCompilerSimulation (rnnSteps net)
mobiusRNNCompilerSimulation net =
  rnnCompilerSimulation (rnnSteps net)

mobiusRNNAdjointCorrect :
  {A T C R : Set} →
  (net : MobiusRNN A T C R) →
  AdjointLaw (rnnPairing net) (compileMobiusRNN net)
mobiusRNNAdjointCorrect net =
  compiledAdjoint (rnnPairing net) (rnnAdjoints net)
