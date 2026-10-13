{-# OPTIONS --guardedness --no-sized-types #-}

module FullCoupled.FormalMethods.MonoidLSTMStreams where

open import Agda.Builtin.Coinduction using (∞; ♯_; ♭)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

-- A productive stream stores its tail behind Agda's built-in delay.
-- Reflection is deliberately not imported: this semantics does not generate
-- or inspect Agda syntax trees.
data Stream (A : Set) : Set where
  cons : A → ∞ (Stream A) → Stream A

streamHead : {A : Set} → Stream A → A
streamHead (cons value _) = value

streamTail : {A : Set} → Stream A → Stream A
streamTail (cons _ delayed) = ♭ delayed

repeatStream : {A : Set} → A → Stream A
repeatStream value = cons value (♯ repeatStream value)

mapStream : {A B : Set} → (A → B) → Stream A → Stream B
mapStream f (cons value delayed) =
  cons (f value) (♯ mapStream f (♭ delayed))

streamPrefix : {A : Set} → Nat → Stream A → List A
streamPrefix zero _ = []
streamPrefix (suc n) (cons value delayed) =
  value ∷ streamPrefix n (♭ delayed)

mapList : {A B : Set} → (A → B) → List A → List B
mapList f [] = []
mapList f (value ∷ values) = f value ∷ mapList f values

cong :
  {A B : Set} (f : A → B) {left right : A} →
  left ≡ right → f left ≡ f right
cong f refl = refl

trans :
  {A : Set} {left middle right : A} →
  left ≡ middle → middle ≡ right → left ≡ right
trans refl second = second

sym : {A : Set} {left right : A} → left ≡ right → right ≡ left
sym refl = refl

mapListCong :
  {A B : Set} (f : A → B) {left right : List A} →
  left ≡ right → mapList f left ≡ mapList f right
mapListCong f refl = refl

mapStreamPrefix :
  {A B : Set} (n : Nat) (f : A → B) (input : Stream A) →
  streamPrefix n (mapStream f input) ≡
  mapList f (streamPrefix n input)
mapStreamPrefix zero f input = refl
mapStreamPrefix (suc n) f (cons value delayed) =
  cong (λ rest → f value ∷ rest)
    (mapStreamPrefix n f (♭ delayed))

-- Map composition is stated with bisimulation on infinite streams, rather
-- than claiming decidable Leibniz equality for coinductive observations.
mapStreamComposeBisim :
  {A B C : Set}
  (f : B → C)
  (g : A → B)
  (input : Stream A) →
  Bisim (mapStream f (mapStream g input))
    (mapStream (λ value → f (g value)) input)
mapStreamComposeBisim f g (cons value delayed) .headsAgree = refl
mapStreamComposeBisim f g (cons value delayed) .tailsBisimilar =
  ♯ mapStreamComposeBisim f g (♭ delayed)

-- A stateful scan is the basic causal recurrence used by stream-processing
-- programs. An LSTM transition can instantiate step once its concrete state
-- and input types are fixed.
scanStream :
  {State Input : Set} →
  (State → Input → State) →
  State →
  Stream Input →
  Stream State
scanStream step state (cons input delayed) =
  cons
    (step state input)
    (♯ scanStream step (step state input) (♭ delayed))

scanList :
  {State Input : Set} →
  (State → Input → State) →
  State →
  List Input →
  List State
scanList step state [] = []
scanList step state (input ∷ inputs) =
  step state input ∷ scanList step (step state input) inputs

scanListCong :
  {State Input : Set}
  (step : State → Input → State)
  (state : State)
  {left right : List Input} →
  left ≡ right →
  scanList step state left ≡ scanList step state right
scanListCong step state refl = refl

scanStreamPrefix :
  {State Input : Set}
  (n : Nat)
  (step : State → Input → State)
  (state : State)
  (inputs : Stream Input) →
  streamPrefix n (scanStream step state inputs) ≡
  scanList step state (streamPrefix n inputs)
scanStreamPrefix zero step state inputs = refl
scanStreamPrefix (suc n) step state (cons input delayed) =
  cong (λ rest → step state input ∷ rest)
    (scanStreamPrefix n step (step state input) (♭ delayed))

-- A stream transformer is causal at horizon n if equal first-n input samples
-- force equal first-n output samples. These finite-observation predicates do
-- not assume equality of whole infinite streams.
CausalAt :
  {Input Output : Set} →
  Nat →
  (Stream Input → Stream Output) →
  Set
CausalAt n transformer =
  (left right : Stream _) →
  streamPrefix n left ≡ streamPrefix n right →
  streamPrefix n (transformer left) ≡
  streamPrefix n (transformer right)

mapStreamCausalAt :
  {Input Output : Set}
  (n : Nat) (f : Input → Output) →
  CausalAt n (mapStream f)
mapStreamCausalAt n f left right samePrefix =
  trans
    (mapStreamPrefix n f left)
    (trans
      (mapListCong f samePrefix)
      (sym (mapStreamPrefix n f right)))

scanStreamCausalAt :
  {Input State : Set}
  (n : Nat)
  (step : State → Input → State)
  (state : State) →
  CausalAt n (scanStream step state)
scanStreamCausalAt n step state left right samePrefix =
  trans
    (scanStreamPrefix n step state left)
    (trans
      (scanListCong step state samePrefix)
      (sym (scanStreamPrefix n step state right)))

-- The stream comonad exposes each suffix as context. Arbitrary context
-- functions are not automatically zero-lookahead causal; use CausalAt as the
-- explicit admissibility predicate for a causal co-Kleisli arrow.
duplicate : {A : Set} → Stream A → Stream (Stream A)
duplicate input@(cons _ delayed) =
  cons input (♯ duplicate (♭ delayed))

extract : {A : Set} → Stream A → A
extract = streamHead

extend : {A B : Set} → (Stream A → B) → Stream A → Stream B
extend context input = mapStream context (duplicate input)

record Bisim {A : Set} (left right : Stream A) : Set where
  coinductive
  field
    headsAgree : streamHead left ≡ streamHead right
    tailsBisimilar : ∞ (Bisim (streamTail left) (streamTail right))

open Bisim public

bisimReflexive : {A : Set} (input : Stream A) → Bisim input input
bisimReflexive (cons value delayed) .headsAgree = refl
bisimReflexive (cons value delayed) .tailsBisimilar =
  ♯ bisimReflexive (♭ delayed)

extractDuplicateHead :
  {A : Set} (input : Stream A) →
  streamHead (duplicate input) ≡ input
extractDuplicateHead (cons value delayed) = refl

-- This is a coinductive law: prove it by matching each observation and
-- delaying the recursive bisimulation proof instead of claiming stream =.
extendExtractBisimilar :
  {A : Set} (input : Stream A) →
  Bisim (extend extract input) input
extendExtractBisimilar (cons value delayed) .headsAgree = refl
extendExtractBisimilar (cons value delayed) .tailsBisimilar =
  ♯ extendExtractBisimilar (♭ delayed)

ones : Stream Nat
ones = repeatStream (suc zero)

onesPrefixRegression :
  streamPrefix (suc (suc (suc zero))) ones ≡
    suc zero ∷ suc zero ∷ suc zero ∷ []
onesPrefixRegression = refl

runningSum : Stream Nat → Stream Nat
runningSum = scanStream _+_ zero

runningSumPrefixRegression :
  streamPrefix (suc (suc (suc zero))) (runningSum ones) ≡
    suc zero ∷ suc (suc zero) ∷ suc (suc (suc zero)) ∷ []
runningSumPrefixRegression = refl
