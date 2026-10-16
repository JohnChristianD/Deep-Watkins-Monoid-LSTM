{-# OPTIONS --sized-types --no-guardedness #-}

module FullCoupled.FormalMethods.MonoidLSTMStreams where

open import Haskell.Prelude
  using (Nat; zero; suc; List; []; _∷_; _≡_; refl; _+_)
open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Size using (Size; Size<_; ∞)
-- Agda2HS compiles recursive streams through this erased-size lazy tail.
open import Haskell.Prim.Thunk using (Thunk; force)

-- a stream carries the size of the observation depth available to its tail.
-- Each tail is available at a strictly smaller size. This proves productivity
-- through sized recursion rather than the guardedness checker.
-- Agda2HS's supported coinduction encoding: a delayed, sized recursive tail.
data Stream {ℓ : Level} (a : Set ℓ) (@0 i : Size) : Set ℓ where
  streamCons : a → Thunk (Stream a) i → Stream a i

streamHead : {ℓ : Level} {a : Set ℓ} {i : Size} → Stream a i → a
streamHead (streamCons value _) = value

streamTail :
  {ℓ : Level} {a : Set ℓ} {i : Size}
  (input : Stream a i) → {j : Size< i} → Stream a j
streamTail (streamCons _ delayed) {j} = force delayed {j}

{-# COMPILE AGDA2HS Stream #-}
{-# COMPILE AGDA2HS streamHead #-}
{-# COMPILE AGDA2HS streamTail #-}

repeatStream :
  {ℓ : Level} {i : Size} {a : Set ℓ} → a → Stream a i
repeatStream value =
  streamCons value λ where
    .force → repeatStream value

{-# COMPILE AGDA2HS repeatStream #-}

mapStream :
  {ℓa ℓb : Level} {i : Size}
  {a : Set ℓa} {b : Set ℓb} →
  (a → b) → Stream a i → Stream b i
mapStream f input =
  streamCons (f (streamHead input)) λ where
    .force → mapStream f (streamTail input)

{-# COMPILE AGDA2HS mapStream #-}

-- Finite prefixes require an indefinitely observable stream. a merely-sized
-- Stream i may only expose an unknown finite observation depth.
streamPrefix : {ℓ : Level} {a : Set ℓ} → Nat → Stream a ∞ → List a
streamPrefix 0 _ = []
streamPrefix (suc n) input =
  streamHead input ∷ streamPrefix n (streamTail input)

mapList : {ℓa ℓb : Level} {a : Set ℓa} {b : Set ℓb} → (a → b) → List a → List b
mapList f [] = []
mapList f (value ∷ values) = f value ∷ mapList f values

cong :
  {ℓa ℓb : Level} {a : Set ℓa} {b : Set ℓb}
  (f : a → b) {left right : a} →
  left ≡ right → f left ≡ f right
cong f refl = refl

trans :
  {ℓ : Level} {a : Set ℓ} {left middle right : a} →
  left ≡ middle → middle ≡ right → left ≡ right
trans refl second = second

sym : {ℓ : Level} {a : Set ℓ} {left right : a} → left ≡ right → right ≡ left
sym refl = refl

mapListCong :
  {ℓa ℓb : Level} {a : Set ℓa} {b : Set ℓb}
  (f : a → b) {left right : List a} →
  left ≡ right → mapList f left ≡ mapList f right
mapListCong f refl = refl

mapStreamPrefix :
  {ℓa ℓb : Level} {a : Set ℓa} {b : Set ℓb}
  (n : Nat) (f : a → b) (input : Stream a ∞) →
  streamPrefix n (mapStream f input) ≡
  mapList f (streamPrefix n input)
mapStreamPrefix 0 f input = refl
mapStreamPrefix (suc n) f input =
  cong (λ rest → f (streamHead input) ∷ rest)
    (mapStreamPrefix n f (streamTail input))

-- a stateful scan is the causal recurrence used by stream-processing
-- programs. An LSTM transition can instantiate step once state/input types
-- are fixed.
scanStream :
  {ℓs ℓi : Level} {i : Size}
  {state : Set ℓs} {input : Set ℓi} →
  (state → input → state) →
  state → Stream input i → Stream state i
scanStream step state inputs =
  streamCons (step state (streamHead inputs)) λ where
    .force →
      scanStream
        step
        (step state (streamHead inputs))
        (streamTail inputs)

{-# COMPILE AGDA2HS scanStream #-}

-- The learner trace convention includes the initial state at observation zero.
scanSeededStream :
  {ℓs ℓi : Level} {i : Size}
  {state : Set ℓs} {input : Set ℓi} →
  (state → input → state) →
  state → Stream input i → Stream state i
scanSeededStream step state inputs =
  streamCons state λ where
    .force →
      scanSeededStream
        step
        (step state (streamHead inputs))
        (streamTail inputs)

{-# COMPILE AGDA2HS scanSeededStream #-}

iterateStream :
  {ℓ : Level} {i : Size} {a : Set ℓ} →
  (a → a) → a → Stream a i
iterateStream step state =
  streamCons state λ where
    .force → iterateStream step (step state)

{-# COMPILE AGDA2HS iterateStream #-}

iterateList :
  {ℓ : Level} {a : Set ℓ} →
  Nat → (a → a) → a → List a
iterateList zero step state = []
iterateList (suc n) step state =
  state ∷ iterateList n step (step state)

{-# COMPILE AGDA2HS iterateList #-}

scanList :
  {ℓs ℓi : Level} {state : Set ℓs} {input : Set ℓi} →
  (state → input → state) →
  state → List input → List state
scanList step state [] = []
scanList step state (input ∷ inputs) =
  step state input ∷ scanList step (step state input) inputs

scanListCong :
  {ℓs ℓi : Level} {state : Set ℓs} {input : Set ℓi}
  (step : state → input → state)
  (state : state)
  {left right : List input} →
  left ≡ right →
  scanList step state left ≡ scanList step state right
scanListCong step state refl = refl

scanStreamPrefix :
  {ℓs ℓi : Level} {state : Set ℓs} {input : Set ℓi}
  (n : Nat)
  (step : state → input → state)
  (state : state)
  (inputs : Stream input ∞) →
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
iterateStreamPrefix :
  {ℓ : Level} {a : Set ℓ} →
  (n : Nat) (step : a → a) (initial : a) →
  streamPrefix n (iterateStream step initial) ≡
    iterateList n step initial
iterateStreamPrefix zero step initial = refl
iterateStreamPrefix (suc n) step initial =
  cong (λ rest → initial ∷ rest)
    (iterateStreamPrefix n step (step initial))

CausalAt :
  {ℓi ℓo : Level} {input : Set ℓi} {output : Set ℓo} →
  Nat →
  (Stream input ∞ → Stream output ∞) →
  Set (ℓi ⊔ ℓo)
CausalAt {input = input} n transformer =
  (left right : Stream input ∞) →
  streamPrefix n left ≡ streamPrefix n right →
  streamPrefix n (transformer left) ≡
  streamPrefix n (transformer right)

mapStreamCausalAt :
  {ℓi ℓo : Level} {input : Set ℓi} {output : Set ℓo}
  (n : Nat) (f : input → output) →
  CausalAt n (mapStream f)
mapStreamCausalAt n f left right samePrefix =
  trans
    (mapStreamPrefix n f left)
    (trans
      (mapListCong f samePrefix)
      (sym (mapStreamPrefix n f right)))

scanStreamCausalAt :
  {ℓs ℓi : Level} {state : Set ℓs} {input : Set ℓi}
  (n : Nat)
  (step : state → input → state)
  (state : state) →
  CausalAt n (scanStream step state)
scanStreamCausalAt n step state left right samePrefix =
  trans
    (scanStreamPrefix n step state left)
    (trans
      (scanListCong step state samePrefix)
      (sym (scanStreamPrefix n step state right)))

-- Sized stream contexts represent successive suffixes whose available size
-- decreases at each tail. a homogeneous same-size stream of streams would be
-- incorrect: a suffix is available only at a smaller size.
record StreamContext (i : Size) {ℓ : Level} (a : Set ℓ) : Set ℓ where
  coinductive
  field
    contextStream : Stream a i
    contextTail : ∀ {j : Size< i} → StreamContext j a

open StreamContext public

duplicate : {ℓ : Level} {i : Size} {a : Set ℓ} → Stream a i → StreamContext i a
contextStream (duplicate input) = input
contextTail (duplicate input) {j} =
  duplicate (streamTail input {j})

extract : {ℓ : Level} {i : Size} {a : Set ℓ} → Stream a i → a
extract = streamHead

-- a co-Kleisli arrow is a context observation available at every size.
-- extend applies that context to each successive suffix.
extend :
  {ℓa ℓb : Level} {i : Size}
  {a : Set ℓa} {b : Set ℓb} →
  (∀ {j : Size} → Stream a j → b) →
  Stream a i → Stream b i
extend context input =
  streamCons (context (contextStream (duplicate input))) λ where
    .force →
      extend context (contextStream (contextTail (duplicate input)))


record Bisim (i : Size) {ℓ : Level} {a : Set ℓ}
  (left right : Stream a i) : Set ℓ where
  coinductive
  field
    headsAgree : streamHead left ≡ streamHead right
    tailsBisimilar :
      ∀ {j : Size< i} →
      Bisim j (streamTail left {j}) (streamTail right {j})

open Bisim public

-- Map composition is proved coinductively by decreasing the observation size.
mapStreamComposeBisim :
  {ℓ : Level} {i : Size} {a b c : Set ℓ}
  (f : b → c)
  (g : a → b)
  (input : Stream a i) →
  Bisim i
    (mapStream f (mapStream g input))
    (mapStream (λ value → f (g value)) input)
mapStreamComposeBisim f g input .headsAgree = refl
mapStreamComposeBisim f g input .tailsBisimilar {j} =
  mapStreamComposeBisim f g (streamTail input {j})

-- Named fusion law: two successive maps agree with their composed map at
-- every finite observation depth and, by Bisim, over the infinite stream.
mapStreamFusionBisim :
  {ℓ : Level} {i : Size} {a b c : Set ℓ}
  (f : b → c)
  (g : a → b)
  (input : Stream a i) →
  Bisim i
    (mapStream f (mapStream g input))
    (mapStream (λ value → f (g value)) input)
mapStreamFusionBisim = mapStreamComposeBisim

mapListCompose :
  {ℓ : Level} {a b c : Set ℓ} (f : b → c) (g : a → b) (values : List a) →
  mapList f (mapList g values) ≡
  mapList (λ value → f (g value)) values
mapListCompose f g [] = refl
mapListCompose f g (value ∷ values) =
  cong (λ rest → f (g value) ∷ rest) (mapListCompose f g values)

mapStreamFusionPrefix :
  {ℓ : Level} {a b c : Set ℓ}
  (n : Nat) (f : b → c) (g : a → b) (input : Stream a ∞) →
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

-- a state encoding fuses with a scan whenever it commutes with one transition.
-- The proof is coinductive: each tail obligation reduces the commuting square,
-- then recurses at the strictly smaller stream size.
scanMapFusionBisim :
  {ℓs ℓt ℓi : Level} {i : Size}
  {state : Set ℓs} {target : Set ℓt} {input : Set ℓi} →
  (encode : state → target) →
  (step : state → input → state) →
  (targetStep : target → input → target) →
  (stepFusion :
    (state : state) (input : input) →
    encode (step state input) ≡ targetStep (encode state) input) →
  (state : state) (inputs : Stream input i) →
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
  (state : Nat) (inputs : Stream Nat ∞) →
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
  {ℓ : Level} {i : Size} {a : Set ℓ} (input : Stream a i) → Bisim i input input
bisimReflexive input .headsAgree = refl
bisimReflexive input .tailsBisimilar {j} =
  bisimReflexive (streamTail input {j})

extractDuplicateHead :
  {ℓ : Level} {a : Set ℓ} (input : Stream a ∞) →
  streamHead (contextStream (duplicate input)) ≡ streamHead input
extractDuplicateHead input = refl

-- extend extract is identity up to bisimulation, not a claim of decidable
-- Leibniz equality for all infinite observations.
extendExtractBisimilar :
  {ℓ : Level} {i : Size} {a : Set ℓ} (input : Stream a i) →
  Bisim i (extend extract input) input
extendExtractBisimilar input .headsAgree = refl
extendExtractBisimilar input .tailsBisimilar {j} =
  extendExtractBisimilar (streamTail input {j})

ones : Stream Nat ∞
ones = repeatStream (suc zero)

onesPrefixRegression :
  streamPrefix (suc (suc (suc zero))) ones ≡
    suc zero ∷ suc zero ∷ suc zero ∷ []
onesPrefixRegression = refl

runningSum : Stream Nat ∞ → Stream Nat ∞
runningSum = scanStream _+_ zero

runningSumPrefixRegression :
  streamPrefix (suc (suc (suc zero))) (runningSum ones) ≡
    suc zero ∷ suc (suc zero) ∷ suc (suc (suc zero)) ∷ []
runningSumPrefixRegression = refl
