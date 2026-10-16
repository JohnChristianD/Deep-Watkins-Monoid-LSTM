{-# OPTIONS --sized-types --no-guardedness #-}

module FullCoupled.FormalMethods.MonoidLSTMStreams where

open import Agda.Builtin.Size using (Size; Size<_; ∞)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

-- A stream carries the size of the observation depth available to its tail.
-- Each tail is available at a strictly smaller size. This proves productivity
-- through sized recursion rather than the guardedness checker.
record Stream (i : Size) (A : Set) : Set where
  coinductive
  field
    streamHead : A
    streamTail : ∀ {j : Size< i} → Stream j A

open Stream public

repeatStream : {i : Size} {A : Set} → A → Stream i A
streamHead (repeatStream value) = value
streamTail (repeatStream value) {j} = repeatStream value

mapStream :
  {i : Size} {A B : Set} →
  (A → B) → Stream i A → Stream i B
streamHead (mapStream f input) = f (streamHead input)
streamTail (mapStream f input) {j} =
  mapStream f (streamTail input {j})

streamPrefix : {i : Size} {A : Set} → Nat → Stream i A → List A
streamPrefix 0 _ = []
streamPrefix (suc n) input =
  streamHead input ∷ streamPrefix n (streamTail input)

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
  {i : Size} {A B : Set}
  (n : Nat) (f : A → B) (input : Stream i A) →
  streamPrefix n (mapStream f input) ≡
  mapList f (streamPrefix n input)
mapStreamPrefix 0 f input = refl
mapStreamPrefix (suc n) f input =
  cong (λ rest → f (streamHead input) ∷ rest)
    (mapStreamPrefix n f (streamTail input))

-- A stateful scan is the causal recurrence used by stream-processing
-- programs. An LSTM transition can instantiate step once state/input types
-- are fixed.
scanStream :
  {i : Size} {State Input : Set} →
  (State → Input → State) →
  State → Stream i Input → Stream i State
streamHead (scanStream step state inputs) =
  step state (streamHead inputs)
streamTail (scanStream step state inputs) {j} =
  scanStream
    step
    (step state (streamHead inputs))
    (streamTail inputs {j})

scanList :
  {State Input : Set} →
  (State → Input → State) →
  State → List Input → List State
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
  {i : Size} {State Input : Set}
  (n : Nat)
  (step : State → Input → State)
  (state : State)
  (inputs : Stream i Input) →
  streamPrefix n (scanStream step state inputs) ≡
  scanList step state (streamPrefix n inputs)
scanStreamPrefix 0 step state inputs = refl
scanStreamPrefix (suc n) step state inputs =
  cong (λ rest → step state (streamHead inputs) ∷ rest)
    (scanStreamPrefix n step
      (step state (streamHead inputs))
      (streamTail inputs))

-- Equal first-n input samples force equal first-n output samples. This is
-- finite-observation causality, not decidable equality of infinite streams.
CausalAt :
  {Input Output : Set} →
  Nat →
  (Stream ∞ Input → Stream ∞ Output) →
  Set
CausalAt {Input = Input} n transformer =
  (left right : Stream ∞ Input) →
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
  {State Input : Set}
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

-- Sized stream contexts represent successive suffixes whose available size
-- decreases at each tail. A homogeneous same-size stream of streams would be
-- incorrect: a suffix is available only at a smaller size.
record StreamContext (i : Size) (A : Set) : Set where
  coinductive
  field
    contextStream : Stream i A
    contextTail : ∀ {j : Size< i} → StreamContext j A

open StreamContext public

duplicate : {i : Size} {A : Set} → Stream i A → StreamContext i A
contextStream (duplicate input) = input
contextTail (duplicate input) {j} =
  duplicate (streamTail input {j})

extract : {i : Size} {A : Set} → Stream i A → A
extract = streamHead

-- A co-Kleisli arrow is a context observation available at every size.
-- extend applies that context to each successive suffix.
extend :
  {i : Size} {A B : Set} →
  (∀ {j : Size} → Stream j A → B) →
  Stream i A → Stream i B
streamHead (extend context input) =
  context (contextStream (duplicate input))
streamTail (extend context input) {j} =
  extend context (contextStream (contextTail (duplicate input) {j}))

record Bisim (i : Size) {A : Set}
  (left right : Stream i A) : Set where
  coinductive
  field
    headsAgree : streamHead left ≡ streamHead right
    tailsBisimilar :
      ∀ {j : Size< i} →
      Bisim j (streamTail left {j}) (streamTail right {j})

open Bisim public

-- Map composition is proved coinductively by decreasing the observation size.
mapStreamComposeBisim :
  {i : Size} {A B C : Set}
  (f : B → C)
  (g : A → B)
  (input : Stream i A) →
  Bisim i
    (mapStream f (mapStream g input))
    (mapStream (λ value → f (g value)) input)
mapStreamComposeBisim f g input .headsAgree = refl
mapStreamComposeBisim f g input .tailsBisimilar {j} =
  mapStreamComposeBisim f g (streamTail input {j})

-- Named fusion law: two successive maps agree with their composed map at
-- every finite observation depth and, by Bisim, over the infinite stream.
mapStreamFusionBisim :
  {i : Size} {A B C : Set}
  (f : B → C)
  (g : A → B)
  (input : Stream i A) →
  Bisim i
    (mapStream f (mapStream g input))
    (mapStream (λ value → f (g value)) input)
mapStreamFusionBisim = mapStreamComposeBisim

mapListCompose :
  {A B C : Set} (f : B → C) (g : A → B) (values : List A) →
  mapList f (mapList g values) ≡
  mapList (λ value → f (g value)) values
mapListCompose f g [] = refl
mapListCompose f g (value ∷ values) =
  cong (λ rest → f (g value) ∷ rest) (mapListCompose f g values)

mapStreamFusionPrefix :
  {i : Size} {A B C : Set}
  (n : Nat) (f : B → C) (g : A → B) (input : Stream i A) →
  streamPrefix n (mapStream f (mapStream g input)) ≡
  streamPrefix n (mapStream (λ value → f (g value)) input)
mapStreamFusionPrefix n f g input =
  trans
    (mapStreamPrefix n f (mapStream g input))
    (trans
      (mapListCong f (mapStreamPrefix n g input))
      (trans
        (mapListCompose f g (streamPrefix n input))
        (sym (mapStreamPrefix n (λ value → f (g value)) input))))

-- A state encoding fuses with a scan whenever it commutes with one transition.
-- The proof is coinductive: each tail obligation reduces the commuting square,
-- then recurses at the strictly smaller stream size.
scanMapFusionBisim :
  {i : Size} {State Target Input : Set} →
  (encode : State → Target) →
  (step : State → Input → State) →
  (targetStep : Target → Input → Target) →
  (stepFusion :
    (state : State) (input : Input) →
    encode (step state input) ≡ targetStep (encode state) input) →
  (state : State) (inputs : Stream i Input) →
  Bisim i
    (mapStream encode (scanStream step state inputs))
    (scanStream targetStep (encode state) inputs)
scanMapFusionBisim encode step targetStep stepFusion state inputs
  .headsAgree =
    stepFusion state (streamHead inputs)
scanMapFusionBisim encode step targetStep stepFusion state inputs
  .tailsBisimilar {j}
  rewrite sym (stepFusion state (streamHead inputs)) =
    scanMapFusionBisim
      encode
      step
      targetStep
      stepFusion
      (step state (streamHead inputs))
      (streamTail inputs {j})

-- Regression: successor encoding commutes with natural-number addition.
-- Mapping successor over a running sum agrees with starting the scan
-- from the successor state, at every finite observation and over the stream.
scanSuccessorFusionStep :
  (state input : Nat) →
  suc (state + input) ≡ suc state + input
scanSuccessorFusionStep state input = refl

scanSuccessorFusionRegression :
  (state : Nat) (inputs : Stream ∞ Nat) →
  Bisim ∞
    (mapStream suc (scanStream _+_ state inputs))
    (scanStream _+_ (suc state) inputs)
scanSuccessorFusionRegression state inputs =
  scanMapFusionBisim
    suc
    _+_
    _+_
    scanSuccessorFusionStep
    state
    inputs

bisimReflexive :
  {i : Size} {A : Set} (input : Stream i A) → Bisim i input input
bisimReflexive input .headsAgree = refl
bisimReflexive input .tailsBisimilar {j} =
  bisimReflexive (streamTail input {j})

extractDuplicateHead :
  {A : Set} (input : Stream ∞ A) →
  streamHead (contextStream (duplicate input)) ≡ streamHead input
extractDuplicateHead input = refl

-- extend extract is identity up to bisimulation, not a claim of decidable
-- Leibniz equality for all infinite observations.
extendExtractBisimilar :
  {i : Size} {A : Set} (input : Stream i A) →
  Bisim i (extend extract input) input
extendExtractBisimilar input .headsAgree = refl
extendExtractBisimilar input .tailsBisimilar {j} =
  extendExtractBisimilar (streamTail input {j})

ones : Stream ∞ Nat
ones = repeatStream (suc zero)

onesPrefixRegression :
  streamPrefix (suc (suc (suc zero))) ones ≡
    suc zero ∷ suc zero ∷ suc zero ∷ []
onesPrefixRegression = refl

runningSum : Stream ∞ Nat → Stream ∞ Nat
runningSum = scanStream _+_ zero

runningSumPrefixRegression :
  streamPrefix (suc (suc (suc zero))) (runningSum ones) ≡
    suc zero ∷ suc (suc zero) ∷ suc (suc (suc zero)) ∷ []
runningSumPrefixRegression = refl
