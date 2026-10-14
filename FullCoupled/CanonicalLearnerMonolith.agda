{-# OPTIONS
  --lossy-unification
  --experimental-lazy-instances
  --sized-types
  --exact-split
  --no-projection-like
  --erased-matches
  --erase-record-parameters
  --prop
  --confluence-check
  --two-level
  --rewriting
  --level-universe
  --cumulativity
  --auto-inline
  --polarity
  --flat-split
  -v=1
#-}

------------------------------------------------------------------------
-- Canonical learner semantics.
--
-- This module is the executable/type-level source of the coupled learner:
-- recurrent monoid-LSTM state, Watkins state, custom q-projected sign-IDBD w/ coupled L2 optimizer state,
-- LCB counts, sparse policy readout, q-log state, the persistent learner channels, and the
-- endogenous feedback signal. The definitions below determine what the
-- learner actually does; theorem modules consume these definitions.
--
-- The main emergent facts are structural: LCB totalCount advances exactly
-- by one per canonical step, the optimizer state is explicit, the policy is
-- invariant under optimizer replacement, and the recurrent
-- components are exposed as composable monoid-LSTM state transitions. The integer
-- token layer and Haar-featured linear transformer are exact formal substrates, not
-- empirical language-model or physical-realism claims.
--
-- This file intentionally contains definitions and local definitional laws,
-- not economic existence conclusions. Convergence, fixed points, market
-- clearing, supporting prices, and Walrasian existence require independent
-- hypotheses and belong to the theorem/economic boundary documented outside
-- this module.
------------------------------------------------------------------------

module FullCoupled.CanonicalLearnerMonolith where

-- Merged external import surface; internal FullCoupled imports remain module-local.
open import Haskell.Prelude public
open import Haskell.Law public
open import Haskell.Law.Ord.Ordering public
open import Haskell.Law.Equality public
open import Haskell.Law.Extensionality public
open import Haskell.Law.Functor.FromMonad public
open import Haskell.Law.Semigroup.List public
open import Haskell.Law.Nat public
open import Haskell.Law.Monad.List public
open import Haskell.Law.Monoid.List public
open import Haskell.Law.Ord.Ordering public
open import Haskell.Prim.Thunks public
open import Haskell.Prim.Equality public
open import Haskell.Prim.Absurd public
open import Haskell.Prim.Applicative public
open import Haskell.Extra.Delay public
open import Haskell.Extra.Erase public
open import Haskell.Extra.Nat public
open import Haskell.Control.Exception public
open import Agda.Builtin.Equality public
open import Agda.Builtin.Equality.Rewrite public
open import Agda.Builtin.Reflection public
open import Agda.Builtin.Coinduction public
open import Agda.Builtin.Size public

variable
  ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
  A B C       : Set ℓ
  P Q         : A → Set ℓ
  x y z       : A
  f g h       : (x : A) → P x
  b b₁ b₂ b₃  : Bool
  k l m n     : Nat
  xs ys zs    : List A

cong : (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

transport : (P : A → Set ℓ) → x ≡ y → P x → P y
transport P refl p = p

+comm : m + n ≡ n + m
+comm {m = zero}  = refl
+comm {m = suc m} = cong suc (+comm {m = m})

zero+ : zero + n ≡ n
zero+ = refl

suc+ : (suc m) + n ≡ suc (m + n)
suc+ = refl

+zero : m + zero ≡ m
+zero {m = zero}  = refl
+zero {m = suc m} = cong suc +zero

+suc : m + (suc n) ≡ suc (m + n)
+suc {m = zero}  = refl
+suc {m = suc m} = cong suc +suc

{-# REWRITE +zero +suc #-}

+comm : m + n ≡ n + m
+comm {m = zero}  = refl
+comm {m = suc m} = cong suc (+comm {m = m})

map : (A → B) → List A → List B
map f []       = []
map f (x ∷ xs) = (f x) ∷ (map f xs)

infixr 5 _++_
_++_ : List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

map-id : map (λ x → x) xs ≡ xs
map-id {xs = []}     = refl
map-id {xs = x ∷ xs} = cong (_∷_ x) map-id

map-fuse : map f (map g xs) ≡ map (λ x → f (g x)) xs
map-fuse {xs = []}     = refl
map-fuse {xs = x ∷ xs} = cong (_∷_ _) map-fuse

map-++ : map f (xs ++ ys) ≡ (map f xs) ++ (map f ys)
map-++ {xs = []}     = refl
map-++ {xs = x ∷ xs} = cong (_∷_ _) (map-++ {xs = xs})

{-# REWRITE map-id map-fuse map-++ #-}

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B
open _×_

swap : A × B → B × A
swap (x , y) = y , x

test₁ : map swap (map swap xs ++ map swap ys) ≡ xs ++ ys
test₁ = refl

-- Using map-++:
step₁ : map swap (map swap xs ++ map swap ys)
      ≡ map swap (map swap xs) ++ map swap (map swap ys)
step₁ = refl

-- Using map-fuse (likewise for ys)
step₂ : map swap (map swap xs)
      ≡ map (λ x → swap (swap x)) xs
step₂ = refl

-- Using eta-expansion
step₃ : map (λ x → swap (swap x)) xs
      ≡ map (λ x → swap (swap (fst x , snd x))) xs
step₃ = refl

-- Using definition of swap (2x)
step₄ : map (λ x → swap (swap (fst x , snd x))) xs
      ≡ map (λ x → (fst x , snd x)) xs
step₄ = refl

-- Using map-id (together with eta-contraction)
step₅ : map (λ x → (fst x , snd x)) xs ≡ xs
step₅ = refl

postulate
  Circle : Set
  base : Circle
  loop : base ≡ base

postulate
  Circle-elim : (P : Circle → Set ℓ)
    → (base* : P base)
    → (loop* : transport P loop base* ≡ base*)
    → (x : Circle) → P x
  elim-base : ∀ (P : Circle → Set ℓ) base* loop*
    → Circle-elim P base* loop* base ≡ base*
{-# REWRITE elim-base #-}

apd : (f : (x : A) → P x) (p : x ≡ y)
    → transport P p (f x) ≡ f y
apd f refl = refl

postulate
  elim-loop : ∀ (P : Circle → Set ℓ) base* loop*
    → apd (Circle-elim P base* loop*) loop ≡ loop*
{-# REWRITE elim-loop #-}


data _≐_ {A : Set ℓ} (x : A) : A → Prop ℓ where
  refl : x ≐ x

postulate
  transportR : (P : A → Set ℓ) → x ≐ y → P x → P y
  transportR-refl : transportR P refl x ≡ x
{-# REWRITE transportR-refl #-}

variable
  R : A → A → Prop

postulate
  _//_    : (A : Set ℓ) (R : A → A → Prop) → Set ℓ
  proj    : A → A // R
  quot    : R x y → proj {R = R} x ≐ proj {R = R} y

  //-elim : (P : A // R → Set ℓ)
    → (proj* : (x : A) → P (proj x))
    → (quot* : {x y : A} (r : R x y)
             → transportR P (quot r) (proj* x) ≐ proj* y)
    → (x : A // R) → P x
  //-beta : {R : A → A → Prop} (P : A // R → Set ℓ)
    → (proj* : (x : A) → P (proj x))
    → (quot* : {x y : A} (r : R x y)
             → transportR P (quot r) (proj* x) ≐ proj* y)
    → {u : A} → //-elim P proj* quot* (proj u) ≡ proj* u
  -- Note: The type of //-beta mysteriously does not
  -- check when I leave out the {R : A → A → Prop},
  -- I'm not sure what's up with that.
{-# REWRITE //-beta #-}

postulate
  Exc : Set
  runtimeException : Exc
  raise : Exc → A

  raise-suc : {e : Exc} → suc (raise e) ≡ raise e

  raise-fun : {e : Exc}
    → raise {A = (x : A) → P x} e
    ≡ λ x → raise {A = P x} e

{-# REWRITE raise-suc raise-fun #-}

postulate
  catch-Bool : (P : Bool → Set ℓ)
               (pt : P true) (pf : P false)
               (h : ∀ e → P (raise e))
             → (b : Bool) → P b

  catch-true  : ∀ (P : Bool → Set ℓ) pt pf h
              → catch-Bool P pt pf h true ≡ pt
  catch-false : ∀ (P : Bool → Set ℓ) pt pf h
              → catch-Bool P pt pf h false ≡ pf
  catch-exc   : ∀ (P : Bool → Set ℓ) pt pf h e
              → catch-Bool P pt pf h (raise e) ≡ h e

{-# REWRITE catch-true catch-false catch-exc #-}

record ⊤ {ℓ} : Prop ℓ where constructor tt

data   ⊥ {ℓ} : Prop ℓ where

record _∧_ (X : Prop ℓ₁) (Y : Prop ℓ₂) : Prop (ℓ₁ ⊔ ℓ₂) where
  constructor _,_
  field
    fst : X
    snd : Y
open _∧_

infix 6 _≅_
-- Observational equality
postulate
  _≅_ : {A : Set ℓ₁} {B : Set ℓ₂} → A → B → Prop (ℓ₁ ⊔ ℓ₂)

HEq = _≅_
syntax HEq {A = A} {B = B} x y = x ∈ A ≅ y ∈ B

postulate
  refl-Bool   : (Bool  ≅ Bool)  ≡ ⊤
  refl-true   : (true  ≅ true)  ≡ ⊤
  refl-false  : (false ≅ false) ≡ ⊤
  conflict-tf : (true  ≅ false) ≡ ⊥
  conflict-ft : (false ≅ true)  ≡ ⊥
{-# REWRITE refl-Bool refl-true refl-false
            conflict-tf conflict-ft #-}

postulate
  cong-Π : ((x : A) → P x) ≅ ((y : B) → Q y)
         ≡ (B ≅ A) ∧ ((x : A)(y : B) → y ≅ x → P x ≅ Q y)
  cong-λ : {A : Set ℓ₁} {B : Set ℓ₂}
    → {P : A → Set ℓ₃} {Q : B → Set ℓ₄}
    → (f : (x : A) → P x) (g : (y : B) → Q y)
    → ((λ x → f x) ≅ (λ y → g y))
    ≡ ((x : A) (y : B) (x≅y : x ≅ y) → f x ≅ g y)
{-# REWRITE cong-Π cong-λ #-}

infix 10 _[_⟩ _||_

postulate
  _[_⟩    : A → A ≅ B → B         -- Coercion
  _||_    : (x : A) (Q : A ≅ B)
          → x ∈ A ≅ x [ Q ⟩ ∈ B   -- Coherence

postulate
  coerce-Bool : b [ tt ⟩ ≡ b
{-# REWRITE coerce-Bool #-}

postulate
  coerce-Π : {A : Set ℓ₁} {B : Set ℓ₂}
    → {P : A → Set ℓ₃} {Q : B → Set ℓ₄}
    → {f : (x : A) → P x}
    → (ΠAP≅ΠBQ : ((x : A) → P x) ≅ ((y : B) → Q y))
    → _≡_ {A = (y : B) → Q y} (f [ ΠAP≅ΠBQ ⟩) λ (y : B) →
        let B≅A : B ≅ A
            B≅A = fst ΠAP≅ΠBQ
            x   : A
            x   = y [ B≅A ⟩
            Px≅Qy : P x ≅ Q y
            Px≅Qy = snd ΠAP≅ΠBQ x y (_||_ {B = A} y B≅A)
        in f x [ Px≅Qy ⟩
{-# REWRITE coerce-Π #-}



Int : Set
Int = ℤ

infixl 31 _+Int_
_+Int_ : Int → Int → Int
_+Int_ = _ℤ+_

infixl 31 _*Int_
_*Int_ : Int → Int → Int
_*Int_ = _ℤ*_


cong₂ : ∀ {A B C : Set} (f : A → B → C) {x y : A} {u v : B} → x ＝ y → u ＝ v → f x u ＝ f y v
cong₂ f refl refl = refl

trans : ∀ {A : Set} {x y z : A} → x ＝ y → y ＝ z → x ＝ z
trans refl q = q



record Int8 : Set where
  constructor int8
  field code : Int
open Int8 public

int8StateSpace : Set
int8StateSpace = Int

zero8 : Int8
zero8 = int8 (pos 0)

one8 : Int8
one8 = int8 (pos 1)

int8OfNat : ℕ → Int8
int8OfNat n = int8 (pos n)

int8Add : Int8 → Int8 → Int8
int8Add x y = int8 (code x +Int code y)

int8Mul : Int8 → Int8 → Int8
int8Mul x y = int8 (code x *Int code y)

intNeg : Int → Int
intNeg (pos zero) = pos zero
intNeg (pos (succ n)) = negsucc n
intNeg (negsucc n) = pos (succ n)

int8Neg : Int8 → Int8
int8Neg x = int8 (intNeg (code x))

int8Sub : Int8 → Int8 → Int8
int8Sub x y = int8 (code x +Int code (int8Neg y))

int8+-assoc : ∀ a b c → int8Add (int8Add a b) c ＝ int8Add a (int8Add b c)
int8+-assoc a b c = ap int8 (ℤ+-assoc (code a) (code b) (code c))

int8*-assoc : ∀ a b c → int8Mul (int8Mul a b) c ＝ int8Mul a (int8Mul b c)
int8*-assoc a b c = ap int8 (ℤ*-assoc (code a) (code b) (code c))

sym : ∀ {A : Set} {x y : A} → x ＝ y → y ＝ x
sym refl = refl

int8*-distribˡ : ∀ a b c → int8Mul a (int8Add b c) ＝ int8Add (int8Mul a b) (int8Mul a c)
int8*-distribˡ a b c =
  ap int8 (distributivity-mult-over-ℤ' (code b) (code c) (code a))

int8*-idˡ : ∀ a → int8Mul one8 a ＝ a
int8*-idˡ a = ap int8 (ℤ-mult-left-id (code a))

int8*-idʳ : ∀ a → int8Mul a one8 ＝ a
int8*-idʳ a = ap int8 (ℤ-mult-right-id (code a))

int8*-zeroʳ : ∀ a → int8Mul a zero8 ＝ zero8
int8*-zeroʳ a = ap int8 (ℤ-zero-right-is-zero (code a))

int8*-zeroˡ : ∀ a → int8Mul zero8 a ＝ zero8
int8*-zeroˡ a = ap int8 (ℤ-zero-left-base (code a))

int8+-idˡ : ∀ a → int8Add zero8 a ＝ a
int8+-idˡ a = ap int8 (ℤ-zero-left-neutral (code a))

int8+-idʳ : ∀ a → int8Add a zero8 ＝ a
int8+-idʳ a = ap int8 (ℤ-zero-right-neutral (code a))

int8Roundtrip : ∀ n → code (int8OfNat n) ＝ pos n
int8Roundtrip n = refl



plus-zero : ∀ n → n + zero ＝ n
plus-zero zero = refl
plus-zero (succ n) = ap succ (plus-zero n)

plus-succ : ∀ (m n : ℕ) → m + succ n ＝ succ (m + n)
plus-succ zero n = refl
plus-succ (succ m) n = refl

plus-succ-lt : ∀ (m n : ℕ) → m <ℕ (m + succ n)
plus-succ-lt m zero = ≤-refl (succ m)
plus-succ-lt m (succ n) = ≤-+ m (succ n)

plus-succ-not-self : ∀ (m n : ℕ) → m + succ n ≠ m
plus-succ-not-self m n eq =
  not-less-than-itself m (transport (λ z → m <ℕ z) eq (plus-succ-lt m n))

succ-succ-lt : ∀ (n : ℕ) → n <ℕ succ (succ n)
succ-succ-lt zero = ≤-succ zero
succ-succ-lt (succ n) = ≤-succ (succ n)

succ-succ-not-self : ∀ n → succ (succ n) ≠ n
succ-succ-not-self n eq =
  not-less-than-itself (succ (succ n))
    (transport (λ z → z <ℕ succ (succ n)) (eq ⁻¹) (succ-succ-lt n))

iterate : ∀ {S : Set} → (S → S) → ℕ → S → S
iterate step zero s = s
iterate step (succ n) s = step (iterate step n s)

OrbitNonFixed : ∀ {S : Set} {step : S → S} → S → Set
OrbitNonFixed {step = step} s = ∀ n → iterate step n s ≠ step (iterate step n s)

data Signed : Set where
  signedNeg : ℕ → Signed
  signedZer : Signed
  signedPos : ℕ → Signed

signedCode : Int8 → Signed
signedCode (int8 (pos 0)) = signedZer
signedCode (int8 (pos (succ n))) = signedPos (succ n)
signedCode (int8 (negsucc n)) = signedNeg (succ n)

data BoolLike : Set where
  enabled disabled : BoolLike

record ActionSpace (A : Set) : Set where
  constructor actionSpace
  field
    candidates : List ℕ
    witness : ℕ
open ActionSpace public

QFunction : ∀ {A : Set} → Set
QFunction {A} = ℕ → Int8

CountFunction : ∀ {A : Set} → Set
CountFunction {A} = ℕ → ℕ

zeroQ : ∀ {A : Set} → QFunction {A}
zeroQ _ = zero8

zeroCounts : ∀ {A : Set} → CountFunction {A}
zeroCounts _ = zero

natEq : ℕ → ℕ → BoolLike
natEq zero zero = enabled
natEq zero (succ n) = disabled
natEq (succ m) zero = disabled
natEq (succ m) (succ n) = natEq m n

natLt : ℕ → ℕ → BoolLike
natLt zero zero = disabled
natLt zero (succ n) = enabled
natLt (succ m) zero = disabled
natLt (succ m) (succ n) = natLt m n

natLE : ℕ → ℕ → BoolLike
natLE zero n = enabled
natLE (succ m) zero = disabled
natLE (succ m) (succ n) = natLE m n

maxNat : ℕ → ℕ → ℕ
maxNat zero n = n
maxNat (succ m) zero = succ m
maxNat (succ m) (succ n) = succ (maxNat m n)

updateAt : ∀ {A : Set} → QFunction {A} → ℕ → Int8 → QFunction {A}
updateAt q a r i with natEq i a
... | enabled = int8Add (q i) r
... | disabled = q i

incAt : ∀ {A : Set} → CountFunction {A} → ℕ → CountFunction {A}
incAt c a i with natEq i a
... | enabled = succ (c i)
... | disabled = c i

record CriticState (A : Set) : Set where
  constructor criticState
  field values : QFunction {A}
open CriticState public

record WatkinsKernel (A : Set) : Set₁ where
  constructor mkWatkinsKernel
  field
    updateCritic : CriticState A → Int8 → CriticState A
    greedy : CriticState A → Int8 → BoolLike
    traceUpdate : BoolLike → BoolLike → BoolLike
open WatkinsKernel public

record WatkinsState (A : Set) : Set where
  constructor watkinsState
  field critic : CriticState A
        signal : Int8
        trace : BoolLike
open WatkinsState public

watkinsStep : ∀ {A : Set} → WatkinsKernel A → WatkinsState A → WatkinsState A
watkinsStep K s = watkinsState
  (updateCritic K (critic s) (signal s))
  (signal s)
  (traceUpdate K (trace s) (greedy K (critic s) (signal s)))

record LCBCountState (A : Set) : Set where
  constructor lcbCountState
  field valuesCount : CountFunction {A}
        totalCount : ℕ
open LCBCountState public

record LCBCountKernel : Set₁ where
  constructor lcbCountKernel
  field bonus : ℕ → Int8
open LCBCountKernel public

finiteLCBBonus8 : ℕ → Int8
finiteLCBBonus8 zero = int8OfNat 127
finiteLCBBonus8 (succ zero) = int8OfNat 63
finiteLCBBonus8 (succ (succ zero)) = int8OfNat 31
finiteLCBBonus8 (succ (succ (succ zero))) = int8OfNat 15
finiteLCBBonus8 (succ (succ (succ (succ zero)))) = int8OfNat 7
finiteLCBBonus8 (succ (succ (succ (succ (succ zero))))) = int8OfNat 3
finiteLCBBonus8 (succ (succ (succ (succ (succ (succ zero)))))) = int8OfNat 1
finiteLCBBonus8 _ = zero8

lcbNegate : Int8 → Int8
lcbNegate x = int8Neg x

scoreA : ∀ {A : Set} → QFunction {A} → CountFunction {A} → ℕ → Int8
scoreA q c a = int8Add (q a) (lcbNegate (finiteLCBBonus8 (c a)))

lcbScore : ∀ {A : Set} → LCBCountKernel → LCBCountState A → CriticState A → QFunction {A}
lcbScore L c q a = int8Add (values q a) (lcbNegate (bonus L (valuesCount c a)))

sparsemaxTemperature : ℕ
sparsemaxTemperature = 16

ScoreEntry : Set
ScoreEntry = Int8 × ℕ

int8-code-injective : ∀ {x y : Int8} → code x ＝ code y → x ＝ y
int8-code-injective refl = refl

scoreList : ∀ {A : Set} → ActionSpace A → QFunction {A} → CountFunction {A} → List ScoreEntry
scoreList {A} K q c = map (λ a → (scoreA {A = A} q c a , a)) (candidates K)

data ComparisonResult : Set where
  less equal greater : ComparisonResult

compareInt8 : Int8 → Int8 → ComparisonResult
compareInt8 x y with ℤ-trichotomous (code x) (code y)
... | inl _ = less
... | inr (inl _) = equal
... | inr (inr _) = greater

compareNat : ℕ → ℕ → ComparisonResult
compareNat zero zero = equal
compareNat zero (succ _) = less
compareNat (succ _) zero = greater
compareNat (succ m) (succ n) = compareNat m n

scoreBefore : ScoreEntry → ScoreEntry → Bool
scoreBefore (s₁ , a₁) (s₂ , a₂) with compareInt8 s₁ s₂
... | less = false
... | greater = true
... | equal with compareNat a₁ a₂
... | less = false
... | equal = true
... | greater = true

insertScore : ScoreEntry → List ScoreEntry → List ScoreEntry
insertScore x [] = x ∷ []
insertScore x (y ∷ ys) with scoreBefore x y
... | true = x ∷ y ∷ ys
... | false = y ∷ insertScore x ys

sortScores : List ScoreEntry → List ScoreEntry
sortScores [] = []
sortScores (x ∷ xs) = insertScore x (sortScores xs)

natAt : ℕ → List ℕ → ℕ
natAt k [] = zero
natAt zero (x ∷ xs) = x
natAt (succ k) (x ∷ xs) = natAt k xs

sumList : List ℕ → ℕ
sumList [] = zero
sumList (x ∷ xs) = x + sumList xs

------------------------------------------------------------------------
-- Integer LayerNorm kernel.
--
-- Int8 is an exact Int wrapper.  The normalization arithmetic therefore
-- remains integral and the normalized output is represented as an exact
-- integer ratio.  A certificate supplies the non-zero square root of
-- the integer radicand; no floating-point approximation enters the
-- proof surface.
------------------------------------------------------------------------

integerCodeSum : List Int8 → Int
integerCodeSum [] = pos 0
integerCodeSum (x ∷ xs) = code x +Int integerCodeSum xs

integerCodeSumList : List Int → Int
integerCodeSumList [] = pos 0
integerCodeSumList (x ∷ xs) = x +Int integerCodeSumList xs

integerLayerNormCenteredNumerator :
  List Int8 → Int8 → Int
integerLayerNormCenteredNumerator xs x =
  (pos (length xs)) *Int code x +Int intNeg (integerCodeSum xs)

integerLayerNormCenteredNumerators :
  List Int8 → List Int
integerLayerNormCenteredNumerators xs =
  map
    (λ x → integerLayerNormCenteredNumerator xs x)
    xs

integerLayerNormSquare : Int → Int
integerLayerNormSquare z = z *Int z

integerLayerNormVarianceNumerator :
  List Int8 → Int
integerLayerNormVarianceNumerator xs =
  integerCodeSumList
    (map
      integerLayerNormSquare
      (integerLayerNormCenteredNumerators xs))

integerLayerNormEpsilonContribution :
  List Int8 → ℕ → Int
integerLayerNormEpsilonContribution xs epsilon =
  code
    (int8Mul
      (int8OfNat epsilon)
      (int8Mul (int8OfNat (length xs)) (int8OfNat (length xs))))

integerLayerNormRadicand :
  List Int8 → ℕ → Int
integerLayerNormRadicand xs epsilon =
  integerLayerNormVarianceNumerator xs
  +Int
  integerLayerNormEpsilonContribution xs epsilon

record IntegerLayerNormConfig : Set where
  constructor integerLayerNormConfig
  field fixedScale gamma beta : Int8
open IntegerLayerNormConfig public

record IntegerLayerNormCertificate
  (xs : List Int8) : Set where
  constructor integerLayerNormCertificate
  field
    epsilon : ℕ
    root : ℕ
    rootSquared :
      code
        (int8Mul (int8OfNat root) (int8OfNat root)) ＝
      integerLayerNormRadicand xs epsilon
    rootNonZero : root ≠ zero
open IntegerLayerNormCertificate public

record IntegerLayerNormValue : Set where
  constructor mkIntegerLayerNormValue
  field
    numerator : Int
    denominator : ℕ
    denominatorNonZero : denominator ≠ zero
open IntegerLayerNormValue public

integerLayerNormValue :
  ∀ {xs : List Int8} →
  IntegerLayerNormConfig →
  IntegerLayerNormCertificate xs →
  Int8 →
  IntegerLayerNormValue
integerLayerNormValue {xs} config certificate x =
  mkIntegerLayerNormValue
    (code (gamma config) *Int
      (code (fixedScale config) *Int
        integerLayerNormCenteredNumerator xs x)
     +Int
     (code (beta config) *Int (pos (root certificate))))
    (root certificate)
    (rootNonZero certificate)


int8Magnitude : Int8 → ℕ
int8Magnitude (int8 (pos n)) = n
int8Magnitude (int8 (negsucc n)) = succ n

infixl 6 _∸_
_∸_ : ℕ → ℕ → ℕ
zero ∸ n = zero
succ m ∸ zero = succ m
succ m ∸ succ n = m ∸ n

topCodes : ℕ → List ScoreEntry → List ℕ
topCodes zero xs = []
topCodes (succ k) [] = []
topCodes (succ k) ((x , a) ∷ xs) = int8Magnitude x ∷ topCodes k xs

-- TypeTopology arithmetic aliases stay local: do not import the agda2hs
-- Prelude here, since its builtin Nat is a different source type.
infixl 7 _*ℕ_
_*ℕ_ : ℕ → ℕ → ℕ
x *ℕ zero = zero
x *ℕ succ y = x + x *ℕ y

infixl 6 _+ℕ_
_+ℕ_ : ℕ → ℕ → ℕ
_+ℕ_ = _+_

supportValid : List ScoreEntry → ℕ → ℕ → BoolLike
supportValid xs temperature k with natLt (sumList (topCodes k xs)) (((k *ℕ natAt (k ∸ 1) (topCodes k xs)) +ℕ temperature))
... | enabled = enabled
... | disabled = disabled

searchSupport : List ScoreEntry → ℕ → ℕ → ℕ → ℕ → ℕ
searchSupport xs temperature zero current best = best
searchSupport xs temperature (succ n) current best with supportValid xs temperature current
... | enabled = searchSupport xs temperature n (succ current) (maxNat best current)
... | disabled = searchSupport xs temperature n (succ current) best

supportSize : ∀ {A : Set} → ActionSpace A → QFunction {A} → CountFunction {A} → ℕ
supportSize K q c = searchSupport (sortScores (scoreList K q c)) sparsemaxTemperature (length (candidates K)) (succ zero) (succ zero)

record SparseWeight : Set where
  constructor sparseWeight
  field numerator denominator : ℕ
open SparseWeight public

sparsemaxWeight : ∀ {A : Set} → ActionSpace A → QFunction {A} → CountFunction {A} → ℕ → SparseWeight
sparsemaxWeight {A} K q c a = sparseWeight (((k *ℕ int8Magnitude (scoreA {A = A} q c a)) +ℕ sparsemaxTemperature) ∸ s) (k *ℕ sparsemaxTemperature)
  where
    xs = sortScores (scoreList K q c)
    k = supportSize K q c
    s = sumList (topCodes k xs)

weightPositive : SparseWeight → BoolLike
weightPositive (sparseWeight n d) with natEq n zero
... | enabled = disabled
... | disabled = enabled

selectPositive : ∀ {A : Set} → ActionSpace A → QFunction {A} → CountFunction {A} → List ScoreEntry → ℕ
selectPositive K q c [] = witness K
selectPositive K q c ((s , a) ∷ xs) with weightPositive (sparsemaxWeight K q c a)
... | enabled = a
... | disabled = selectPositive K q c xs

sparsemaxPolicy : ∀ {A : Set} → ActionSpace A → QFunction {A} → CountFunction {A} → ℕ
sparsemaxPolicy K q c = selectPositive K q c (sortScores (scoreList K q c))

------------------------------------------------------------------------
-- Exact sparsemax behavior-policy readout.
-- The weight map is kept separate from the selected-action policy.
-- No probability normalization is claimed by this definition.
------------------------------------------------------------------------

updateLCBCount : ∀ {A : Set} → ℕ → LCBCountState A → LCBCountState A
updateLCBCount {A} a (lcbCountState counts total) =
  lcbCountState (incAt {A = A} counts a) (succ total)

------------------------------------------------------------------------
-- TypeTopology Rationals supplies the canonical exact rational carrier.
-- The legacy Dyadic helper names remain stable for theorem/registry
-- surfaces, but their carrier is now TypeTopology's rational type.
------------------------------------------------------------------------

Dyadic : Set
Dyadic = ℚ

fromNatDyadic : ℕ → ℕ → Dyadic
fromNatDyadic n exponent =
  toℚ (pos n , exponent)

dyadicNumerator : Dyadic → ℕ
dyadicNumerator ((pos n , d) , _) = n
dyadicNumerator ((negsucc n , d) , _) = zero

dyadicDenominator : Dyadic → ℕ
dyadicDenominator ((z , d) , _) =
  succ d

dyadicDivide : ℕ → Dyadic → ℕ
dyadicDivide n ((z , d) , _) =
  pr₁ (division n d)

qLog8 : Int8 → Dyadic
qLog8 x with int8Magnitude x
... | zero = fromNatDyadic 1 zero
... | succ n = fromNatDyadic (128 ∸ succ n) (succ n)

munchausenScale8 : ℕ
munchausenScale8 = 16

signedDyadicBias8 : Dyadic → Int8
signedDyadicBias8 q with dyadicNumerator q
... | zero = zero8
... | succ n = int8Neg
  (int8OfNat
    (dyadicDivide
      (munchausenScale8 *ℕ succ n)
      q))

qLog2Bias8 : Int8 → Int8
qLog2Bias8 x =
  signedDyadicBias8 (qLog8 x)

negativeAlpha8 : Int8
negativeAlpha8 = int8OfNat 255

record SignedQLogControl : Set where
  constructor signedQLogControl
  field mode coefficient : Int8
open SignedQLogControl public

canonicalQLogControl : SignedQLogControl
canonicalQLogControl =
  signedQLogControl negativeAlpha8 negativeAlpha8

qLogSignal : SignedQLogControl → Int8 → Int8
qLogSignal c x = int8Add x (coefficient c)

data HardSign : Set where
  negativeSign zeroSign positiveSign : HardSign

hardSignNonnegative : Int8 → HardSign
hardSignNonnegative (int8 (pos 0)) = zeroSign
hardSignNonnegative (int8 (pos (succ n))) = positiveSign
hardSignNonnegative (int8 (negsucc n)) = negativeSign

hardSign : Int8 → HardSign
hardSign (int8 (pos 0)) = zeroSign
hardSign (int8 (pos (succ n))) = positiveSign
hardSign (int8 (negsucc n)) = negativeSign

hardSignGate : Int8 → Int8
hardSignGate x with hardSign x
... | negativeSign = int8OfNat 255
... | zeroSign = zero8
... | positive = one8

two8 : Int8
two8 = int8Add one8 one8

relu8 : Int8 → Int8
relu8 x with hardSign x
... | negativeSign = zero8
... | zeroSign = zero8
... | positive = x

leaky2 : Int8 → Int8
leaky2 x with hardSign x
... | negativeSign = int8Mul two8 x
... | zeroSign = zero8
... | positive = x

------------------------------------------------------------------------
-- Monoid LSTM recurrent core.
--
-- One input acts as an affine endomorphism of cell state.  Affine
-- composition is the carrier monoid; recurrent prefixes therefore admit
-- exact scan composition.  Hidden state is derived from the new cell
-- state plus the signed input feature.  Persistent matrix/noise/control
-- channels remain explicit learner state, preserving the old theorem
-- surface needed by downstream modules without retaining GRU dynamics.
------------------------------------------------------------------------

record MonoidLSTMMatrices : Set where
  constructor monoidLSTMMatrices
  field matrixZ matrixR matrixH : Int8
open MonoidLSTMMatrices public

record MonoidLSTMNoise : Set where
  constructor monoidLSTMNoise
  field noiseZ noiseR noiseH : Int8
open MonoidLSTMNoise public

record MonoidLSTMControl : Set where
  constructor monoidLSTMControl
  field optimizerToken l2Token : Int8
open MonoidLSTMControl public

record MonoidAffine : Set where
  constructor monoidAffine
  field slope offset : Int8
open MonoidAffine public

_∘ₘ_ : MonoidAffine → MonoidAffine → MonoidAffine
(monoidAffine a₁ b₁) ∘ₘ (monoidAffine a₂ b₂) =
  monoidAffine
    (int8Mul a₁ a₂)
    (int8Add (int8Mul a₁ b₂) b₁)

monoidAffine-id : MonoidAffine
monoidAffine-id = monoidAffine one8 zero8

monoidAffine-assoc : ∀ a b c → (a ∘ₘ b) ∘ₘ c ＝ a ∘ₘ (b ∘ₘ c)
monoidAffine-assoc (monoidAffine a₁ b₁) (monoidAffine a₂ b₂) (monoidAffine a₃ b₃) =
  cong₂ monoidAffine
    (int8*-assoc a₁ a₂ a₃)
    (trans
      (cong₂ int8Add
        (int8*-assoc a₁ a₂ b₃)
        refl)
      (trans
        (sym (int8+-assoc
          (int8Mul a₁ (int8Mul a₂ b₃))
          (int8Mul a₁ b₂)
          b₁))
        (ap
          (λ z → int8Add z b₁)
          (sym (int8*-distribˡ
            a₁
            (int8Mul a₂ b₃)
            b₂)))))

monoidAffine-idˡ : ∀ a → monoidAffine-id ∘ₘ a ＝ a
monoidAffine-idˡ (monoidAffine a b) =
  cong₂ monoidAffine
    (int8*-idˡ a)
    (trans
      (ap (λ z → int8Add z zero8) (int8*-idˡ b))
      (int8+-idʳ b))

monoidAffine-idʳ : ∀ a → a ∘ₘ monoidAffine-id ＝ a
monoidAffine-idʳ (monoidAffine a b) =
  cong₂ monoidAffine
    (int8*-idʳ a)
    (trans
      (ap (λ z → int8Add z b) (int8*-zeroʳ a))
      (int8+-idˡ b))

applyMonoidAffine : MonoidAffine → Int8 → Int8
applyMonoidAffine (monoidAffine a b) c =
  int8Add (int8Mul a c) b

data MonoidLSTMGate : Set where
  monoidHold monoidWrite monoidReset monoidAccum : MonoidLSTMGate

monoidLSTMGateOf : Int8 → MonoidLSTMGate
monoidLSTMGateOf (int8 (pos 0)) = monoidHold
monoidLSTMGateOf (int8 (pos (succ n))) = monoidAccum
monoidLSTMGateOf (int8 (negsucc n)) = monoidReset

monoidLSTMCellStep : MonoidLSTMGate → Int8 → Int8 → Int8
monoidLSTMCellStep monoidHold c x = c
monoidLSTMCellStep monoidWrite c x = leaky2 x
monoidLSTMCellStep monoidReset c x = zero8
monoidLSTMCellStep monoidAccum c x = int8Add c (leaky2 x)

monoidLSTMAffineOf : MonoidLSTMGate → Int8 → MonoidAffine
monoidLSTMAffineOf monoidHold x = monoidAffine one8 zero8
monoidLSTMAffineOf monoidWrite x = monoidAffine zero8 (leaky2 x)
monoidLSTMAffineOf monoidReset x = monoidAffine zero8 zero8
monoidLSTMAffineOf monoidAccum x = monoidAffine one8 (leaky2 x)

monoidLSTMCellStep-is-affine :
  ∀ g c x →
  monoidLSTMCellStep g c x ＝
  applyMonoidAffine (monoidLSTMAffineOf g x) c
monoidLSTMCellStep-is-affine monoidHold c x =
  trans
    (sym (int8*-idˡ c))
    (sym (int8+-idʳ (int8Mul one8 c)))
monoidLSTMCellStep-is-affine monoidWrite c x =
  trans
    (sym (int8+-idˡ (leaky2 x)))
    (ap
      (λ z → int8Add z (leaky2 x))
      (sym (int8*-zeroˡ c)))
monoidLSTMCellStep-is-affine monoidReset c x =
  trans
    (sym (int8+-idˡ zero8))
    (ap
      (λ z → int8Add z zero8)
      (sym (int8*-zeroˡ c)))
monoidLSTMCellStep-is-affine monoidAccum c x =
  ap (λ z → int8Add z (leaky2 x)) (sym (int8*-idˡ c))

scanMonoidAffine : List Int8 → MonoidAffine
scanMonoidAffine [] = monoidAffine-id
scanMonoidAffine (x ∷ xs) =
  scanMonoidAffine xs ∘ₘ monoidLSTMAffineOf (monoidLSTMGateOf x) x

scanMonoidAffine-cons :
  ∀ x xs →
  scanMonoidAffine (x ∷ xs) ＝
  scanMonoidAffine xs ∘ₘ monoidLSTMAffineOf (monoidLSTMGateOf x) x
scanMonoidAffine-cons x xs = refl

runMonoidLSTMCell : List Int8 → Int8 → Int8
runMonoidLSTMCell xs c₀ =
  applyMonoidAffine (scanMonoidAffine xs) c₀

record MonoidLSTMState : Set where
  constructor monoidLSTMState
  field
    hiddenState : Int8
    cellState : Int8
    matrixState : MonoidLSTMMatrices
    noiseState : MonoidLSTMNoise
    controlState : MonoidLSTMControl
open MonoidLSTMState public

identityMonoidLSTMMatrices : MonoidLSTMMatrices
identityMonoidLSTMMatrices = monoidLSTMMatrices one8 one8 one8

zeroMonoidLSTMNoise : MonoidLSTMNoise
zeroMonoidLSTMNoise = monoidLSTMNoise zero8 zero8 zero8

zeroMonoidLSTMControl : MonoidLSTMControl
zeroMonoidLSTMControl = monoidLSTMControl zero8 zero8

monoidLSTMHiddenStep : Int8 → Int8 → Int8 → Int8
monoidLSTMHiddenStep h c x =
  int8Add c (leaky2 (int8Add h x))

monoidLSTMStep : MonoidLSTMState → Int8 → MonoidLSTMState
monoidLSTMStep
  (monoidLSTMState h c m n g)
  x =
  let c₁ = monoidLSTMCellStep (monoidLSTMGateOf x) c x
      h₁ = monoidLSTMHiddenStep h c₁ x
  in monoidLSTMState h₁ c₁ m n g

persistentMonoidLSTM :
  MonoidLSTMState →
  MonoidLSTMMatrices × (MonoidLSTMNoise × MonoidLSTMControl)
persistentMonoidLSTM (monoidLSTMState h c m n g) = m , (n , g)

persistentMonoidLSTM-preservation :
  ∀ (s : MonoidLSTMState) (x : Int8) →
  persistentMonoidLSTM (monoidLSTMStep s x) ＝
  persistentMonoidLSTM s
persistentMonoidLSTM-preservation
  (monoidLSTMState h c m n g) x = refl

monoidLSTMParameterPersistence :
  ∀ (s : MonoidLSTMState) (x : Int8) →
  (matrixState (monoidLSTMStep s x) ＝ matrixState s) ×
  ((noiseState (monoidLSTMStep s x) ＝ noiseState s) ×
   (controlState (monoidLSTMStep s x) ＝ controlState s))
monoidLSTMParameterPersistence
  (monoidLSTMState h c m n g) x =
  refl , (refl , refl)

MonoidLSTMEquivalent : MonoidLSTMState → MonoidLSTMState → Set
MonoidLSTMEquivalent s t =
  persistentMonoidLSTM s ＝ persistentMonoidLSTM t

monoidLSTMStep-respects-equivalence :
  ∀ (s t : MonoidLSTMState) (x : Int8) →
  MonoidLSTMEquivalent s t →
  MonoidLSTMEquivalent (monoidLSTMStep s x) (monoidLSTMStep t x)
monoidLSTMStep-respects-equivalence s t x eq =
  trans
    (persistentMonoidLSTM-preservation s x)
    (trans eq (sym (persistentMonoidLSTM-preservation t x)))

------------------------------------------------------------------------
-- Compatibility surface for downstream theorem modules.
-- GRU names are legacy aliases; canonical semantics are MonoidLSTM.
------------------------------------------------------------------------

GRUMatrices : Set
GRUMatrices = MonoidLSTMMatrices

GRUNoise : Set
GRUNoise = MonoidLSTMNoise

GlobalControl : Set
GlobalControl = MonoidLSTMControl

GRUState : Set
GRUState = MonoidLSTMState

gruMatrices : Int8 → Int8 → Int8 → GRUMatrices
gruMatrices a b c = monoidLSTMMatrices a b c

gruNoise : Int8 → Int8 → Int8 → GRUNoise
gruNoise a b c = monoidLSTMNoise a b c

mkGlobalControl : Int8 → Int8 → GlobalControl
mkGlobalControl a b = monoidLSTMControl a b

gruState :
  Int8 →
  Int8 →
  MonoidLSTMMatrices →
  MonoidLSTMNoise →
  MonoidLSTMControl →
  MonoidLSTMState
gruState = monoidLSTMState

identityGRUMatrices : GRUMatrices
identityGRUMatrices = identityMonoidLSTMMatrices

zeroGRUNoise : GRUNoise
zeroGRUNoise = zeroMonoidLSTMNoise

zeroGlobalControl : GlobalControl
zeroGlobalControl = zeroMonoidLSTMControl

dyadicCode : Dyadic → Int8
dyadicCode q = int8OfNat (dyadicNumerator q)

identityActivation8 : Int8 → Int8
identityActivation8 x = x

identityActivation8-law : ∀ x → identityActivation8 x ＝ x
identityActivation8-law x = refl

identityActivation8-zero : identityActivation8 zero8 ＝ zero8
identityActivation8-zero = refl

gruCandidate8 : Int8 → Int8 → Int8
gruCandidate8 h x = int8Add h x

complement128 : Int8 → Int8
complement128 g = int8Sub one8 g

mix8 : Int8 → Int8 → Int8 → Int8
mix8 g old new =
  int8Add
    (int8Mul (complement128 g) old)
    (int8Mul g new)

gateCode : Signed → Int8
gateCode (signedNeg n) = zero8
gateCode signedZer = zero8
gateCode (signedPos n) = one8

gateFromInput : Int8 → Int8
gateFromInput x = gateCode (signedCode x)

monoidLSTMRecurrentStep : MonoidLSTMState → Int8 → MonoidLSTMState
monoidLSTMRecurrentStep = monoidLSTMStep

gruStep : GRUState → Int8 → GRUState
gruStep = monoidLSTMStep

persistentGRU :
  GRUState →
  GRUMatrices × (GRUNoise × GlobalControl)
persistentGRU = persistentMonoidLSTM

persistent-preservation :
  ∀ (s : GRUState) (x : Int8) →
  persistentGRU (gruStep s x) ＝ persistentGRU s
persistent-preservation s x =
  persistentMonoidLSTM-preservation s x

gruParameterPersistence :
  ∀ (s : GRUState) (x : Int8) →
  (matrixState (gruStep s x) ＝ matrixState s) ×
  ((noiseState (gruStep s x) ＝ noiseState s) ×
   (controlState (gruStep s x) ＝ controlState s))
gruParameterPersistence s x =
  monoidLSTMParameterPersistence s x

GRUEquivalent : GRUState → GRUState → Set
GRUEquivalent = MonoidLSTMEquivalent

gruEquivalent-refl : ∀ s → GRUEquivalent s s
gruEquivalent-refl = monoidLSTMEquivalent-refl
  where
    monoidLSTMEquivalent-refl : ∀ s → MonoidLSTMEquivalent s s
    monoidLSTMEquivalent-refl s = refl

gruStep-respects-equivalence :
  ∀ (s t : GRUState) (x : Int8) →
  GRUEquivalent s t →
  GRUEquivalent (gruStep s x) (gruStep t x)
gruStep-respects-equivalence =
  monoidLSTMStep-respects-equivalence

record GRUAction : Set₁ where
  constructor gruAction
  field runGRU : GRUState → GRUState
open GRUAction public

identityGRUAction : GRUAction
identityGRUAction = gruAction (λ s → s)

composeGRUAction : GRUAction → GRUAction → GRUAction
composeGRUAction f g =
  gruAction (λ s → runGRU f (runGRU g s))

gruActionAssociativity : ∀ f g h s →
  runGRU
    (composeGRUAction (composeGRUAction f g) h) s ＝
  runGRU
    (composeGRUAction f (composeGRUAction g h)) s
gruActionAssociativity f g h s = refl

inputGRUAction : Int8 → GRUAction
inputGRUAction x = gruAction (λ s → monoidLSTMStep s x)

record RecurrentNetwork (State Input : Set) : Set₁ where
  constructor recurrentNetwork
  field
    runNetwork : State → Input → State
open RecurrentNetwork public

canonicalMonoidLSTMRecurrentNetwork :
  RecurrentNetwork MonoidLSTMState Int8
canonicalMonoidLSTMRecurrentNetwork =
  recurrentNetwork monoidLSTMStep

canonicalMonoidLSTMNetwork-law :
  ∀ (s : MonoidLSTMState) (x : Int8) →
  runNetwork canonicalMonoidLSTMRecurrentNetwork s x ＝
  monoidLSTMStep s x
canonicalMonoidLSTMNetwork-law s x = refl

canonicalGRURecurrentNetwork : RecurrentNetwork GRUState Int8
canonicalGRURecurrentNetwork =
  recurrentNetwork gruStep

canonicalGRUNetwork-law :
  ∀ (s : GRUState) (x : Int8) →
  runNetwork canonicalGRURecurrentNetwork s x ＝
  monoidLSTMStep s x
canonicalGRUNetwork-law s x = refl

record Endomorphism (State : Set) : Set₁ where
  constructor endomorphism
  field
    applyEndomorphism : State → State
open Endomorphism public

identityEndomorphism : ∀ {State : Set} → Endomorphism State
identityEndomorphism = endomorphism (λ s → s)

composeEndomorphism :
  ∀ {State : Set} →
  Endomorphism State →
  Endomorphism State →
  Endomorphism State
composeEndomorphism f g =
  endomorphism
    (λ s →
      applyEndomorphism f
        (applyEndomorphism g s))

endomorphismAssociative :
  ∀ {State : Set} (f g h : Endomorphism State) s →
  applyEndomorphism
    (composeEndomorphism
      (composeEndomorphism f g)
      h)
    s
  ＝
  applyEndomorphism
    (composeEndomorphism
      f
      (composeEndomorphism g h))
    s
endomorphismAssociative f g h s = refl

recurrentInputEndomorphism :
  ∀ {State Input : Set} →
  RecurrentNetwork State Input →
  Input →
  Endomorphism State
recurrentInputEndomorphism R x =
  endomorphism (λ s → runNetwork R s x)

recurrentPrefixState :
  ∀ {State Input : Set} →
  RecurrentNetwork State Input →
  (ℕ → Input) →
  ℕ →
  State →
  State
recurrentPrefixState R xs zero s = s
recurrentPrefixState R xs (succ n) s =
  runNetwork R
    (recurrentPrefixState R xs n s)
    (xs n)

recurrentPrefixEndomorphism :
  ∀ {State Input : Set} →
  RecurrentNetwork State Input →
  (ℕ → Input) →
  ℕ →
  Endomorphism State
recurrentPrefixEndomorphism R xs zero =
  identityEndomorphism
recurrentPrefixEndomorphism R xs (succ n) =
  composeEndomorphism
    (recurrentInputEndomorphism R (xs n))
    (recurrentPrefixEndomorphism R xs n)

recurrentPrefix-correct :
  ∀ {State Input : Set}
  (R : RecurrentNetwork State Input)
  (xs : ℕ → Input)
  (n : ℕ)
  (s : State) →
  applyEndomorphism
    (recurrentPrefixEndomorphism R xs n)
    s
  ＝
  recurrentPrefixState R xs n s
recurrentPrefix-correct R xs zero s = refl
recurrentPrefix-correct R xs (succ n) s =
  ap
    (λ z → runNetwork R z (xs n))
    (recurrentPrefix-correct R xs n s)

shiftInput :
  ∀ {Input : Set} →
  (ℕ → Input) →
  ℕ →
  ℕ →
  Input
shiftInput xs m n = xs (m + n)

recurrentPrefix-split :
  ∀ {State Input : Set}
  (R : RecurrentNetwork State Input)
  (xs : ℕ → Input)
  (m n : ℕ)
  (s : State) →
  recurrentPrefixState R xs (m + n) s
  ＝
  recurrentPrefixState
    R
    (shiftInput xs m)
    n
    (recurrentPrefixState R xs m s)
recurrentPrefix-split R xs m zero s =
  ap
    (λ k → recurrentPrefixState R xs k s)
    (plus-zero m)
recurrentPrefix-split R xs m (succ n) s =
  trans
    (ap
      (λ k → recurrentPrefixState R xs k s)
      (plus-succ m n))
    (ap
      (λ z → runNetwork R z (xs (m + n)))
      (recurrentPrefix-split R xs m n s))

canonicalMonoidLSTM-recurrent-prefix-correct :
  ∀ (xs : ℕ → Int8) (n : ℕ) (s : MonoidLSTMState) →
  applyEndomorphism
    (recurrentPrefixEndomorphism
      canonicalMonoidLSTMRecurrentNetwork
      xs
      n)
    s
  ＝
  recurrentPrefixState
    canonicalMonoidLSTMRecurrentNetwork
    xs
    n
    s
canonicalMonoidLSTM-recurrent-prefix-correct =
  recurrentPrefix-correct canonicalMonoidLSTMRecurrentNetwork

canonicalMonoidLSTM-recurrent-prefix-split :
  ∀ (xs : ℕ → Int8) (m n : ℕ) (s : MonoidLSTMState) →
  recurrentPrefixState
    canonicalMonoidLSTMRecurrentNetwork
    xs
    (m + n)
    s
  ＝
  recurrentPrefixState
    canonicalMonoidLSTMRecurrentNetwork
    (shiftInput xs m)
    n
    (recurrentPrefixState
      canonicalMonoidLSTMRecurrentNetwork
      xs
      m
      s)
canonicalMonoidLSTM-recurrent-prefix-split =
  recurrentPrefix-split canonicalMonoidLSTMRecurrentNetwork

canonicalGRU-recurrent-prefix-correct :
  ∀ (xs : ℕ → Int8) (n : ℕ) (s : GRUState) →
  applyEndomorphism
    (recurrentPrefixEndomorphism
      canonicalGRURecurrentNetwork
      xs
      n)
    s
  ＝
  recurrentPrefixState
    canonicalGRURecurrentNetwork
    xs
    n
    s
canonicalGRU-recurrent-prefix-correct =
  recurrentPrefix-correct canonicalGRURecurrentNetwork

canonicalGRU-recurrent-prefix-split :
  ∀ (xs : ℕ → Int8) (m n : ℕ) (s : GRUState) →
  recurrentPrefixState
    canonicalGRURecurrentNetwork
    xs
    (m + n)
    s
  ＝
  recurrentPrefixState
    canonicalGRURecurrentNetwork
    (shiftInput xs m)
    n
    (recurrentPrefixState
      canonicalGRURecurrentNetwork
      xs
      m
      s)
canonicalGRU-recurrent-prefix-split =
  recurrentPrefix-split canonicalGRURecurrentNetwork

gruInputActionAssociativity :
  ∀ x y z s →
  runGRU
    (composeGRUAction
      (composeGRUAction
        (inputGRUAction x)
        (inputGRUAction y))
      (inputGRUAction z))
    s
  ＝
  runGRU
    (composeGRUAction
      (inputGRUAction x)
      (composeGRUAction
        (inputGRUAction y)
        (inputGRUAction z)))
    s
gruInputActionAssociativity x y z s = refl


gruStateInt8CoordinateCount : ℕ
gruStateInt8CoordinateCount = 10

criticInt8CoordinateCount : ℕ
criticInt8CoordinateCount = 2

gruPersistentQuotientCoordinateCount : ℕ
gruPersistentQuotientCoordinateCount = 8

fullLearnerInt8CoordinateCount : ℕ
fullLearnerInt8CoordinateCount = 24

fullLearnerInt8CoordinateCount-law : fullLearnerInt8CoordinateCount ＝ 24
fullLearnerInt8CoordinateCount-law = refl

record F4IntUState : Set where
  constructor f4IntUState
  field thetaQ rTheta eQ rE rL : Int8
open F4IntUState public

record F4IntUKernel : Set₁ where
  constructor f4IntUKernel
  field globalL2 : Int8
open F4IntUKernel public

f4ThetaFull : F4IntUState → Int8
f4ThetaFull s = thetaQ s

f4ThetaFull-law : ∀ s → f4ThetaFull s ＝ thetaQ s
f4ThetaFull-law s = refl

l2Correction : Int8 → Int8
l2Correction x = lcbNegate x

f4ThetaStep : F4IntUKernel → F4IntUState → Int8 → F4IntUState
f4ThetaStep K s g =
  f4IntUState
    (int8Add (int8Add (thetaQ s) g) (l2Correction (globalL2 K)))
    zero8 (eQ s) (rE s) (rL s)

f4ParameterInvariant : ∀ (K : F4IntUKernel) (s : F4IntUState) (g : Int8) →
  thetaQ (f4ThetaStep K s g) ＝
  int8Add (int8Add (thetaQ s) g) (l2Correction (globalL2 K))
f4ParameterInvariant K s g = refl

HaarAccumulator : Set
HaarAccumulator = Int8 × Int8


------------------------------------------------------------------------
-- Haar-featured linear transformer.
--
-- Haar mixing remains exact integer arithmetic, now used as a feature map
-- inside a parameterized linear-attention accumulator.  The accumulator
-- is additive and therefore itself forms a monoid; sequence processing is
-- a pure left-to-right scan over rank-one feature updates.
------------------------------------------------------------------------

CanonicalHaarPair : Set
CanonicalHaarPair = Int8 × Int8

canonicalHaarMix : Int8 → Int8 → CanonicalHaarPair
canonicalHaarMix x y =
  int8Add x y , int8Sub x y

canonicalHaarMix-left : ∀ x y →
  pr₁ (canonicalHaarMix x y) ＝ int8Add x y
canonicalHaarMix-left x y = refl

canonicalHaarMix-right : ∀ x y →
  pr₂ (canonicalHaarMix x y) ＝ int8Sub x y
canonicalHaarMix-right x y = refl

canonicalHaarMix-linear-form :
  ∀ x y →
  canonicalHaarMix x y ＝
  (int8Add x y , int8Sub x y)
canonicalHaarMix-linear-form x y = refl

canonicalReLU8 : Int8 → Int8
canonicalReLU8 x with hardSign x
... | negativeSign = zero8
... | zeroSign = zero8
... | positiveSign = x

canonicalCReLU8 : Int8 → CanonicalHaarPair
canonicalCReLU8 x =
  canonicalReLU8 x , canonicalReLU8 (int8Neg x)

------------------------------------------------------------------------
-- Rational CReLU': CReLU with the negative ReLU branch replaced by the
-- exact rational softsign branch, matching the SignReLU shape while
-- keeping the paired positive/negative CReLU representation.
------------------------------------------------------------------------

canonicalSignReLU' : ℚ → ℚ
canonicalSignReLU' (((negsucc n , a) , _)) =
  toℚ (negsucc n , a + succ n)
canonicalSignReLU' q = q

CanonicalCReLUPrimePair : Set
CanonicalCReLUPrimePair = ℚ × ℚ

canonicalCReLU' : ℚ → CanonicalCReLUPrimePair
canonicalCReLU' x =
  canonicalSignReLU' x , canonicalSignReLU' (- x)

canonicalHaarFeature : Int8 → CanonicalHaarPair
canonicalHaarFeature x =
  canonicalHaarMix
    (pr₁ (canonicalCReLU8 x))
    (pr₂ (canonicalCReLU8 x))

canonicalHaarFeature-left : ∀ x →
  pr₁ (canonicalHaarFeature x) ＝
  int8Add
    (pr₁ (canonicalCReLU8 x))
    (pr₂ (canonicalCReLU8 x))
canonicalHaarFeature-left x = refl

canonicalHaarFeature-right : ∀ x →
  pr₂ (canonicalHaarFeature x) ＝
  int8Sub
    (pr₁ (canonicalCReLU8 x))
    (pr₂ (canonicalCReLU8 x))
canonicalHaarFeature-right x = refl

canonicalHaarOrthogonalCross :
  int8Add
    (int8Mul one8 one8)
    (int8Mul one8 (int8Neg one8))
  ＝ zero8
canonicalHaarOrthogonalCross = refl

canonicalHaarFeatureReconstruct :
  ∀ x →
  let p = pr₁ (canonicalCReLU8 x)
      n = pr₂ (canonicalCReLU8 x)
  in int8Sub p n ＝ x
canonicalHaarFeatureReconstruct
  (int8 (pos 0)) = refl
canonicalHaarFeatureReconstruct
  (int8 (pos (succ n))) = refl
canonicalHaarFeatureReconstruct
  (int8 (negsucc n)) = int8+-idˡ (int8 (negsucc n))

canonicalHaarFeatureInjective :
  ∀ {x y} →
  canonicalCReLU8 x ＝ canonicalCReLU8 y →
  x ＝ y
canonicalHaarFeatureInjective {x} {y} eq =
  trans
    (sym (canonicalHaarFeatureReconstruct x))
    (trans
      (cong₂
        (λ a b → int8Sub a b)
        (ap pr₁ eq)
        (ap pr₂ eq))
      (canonicalHaarFeatureReconstruct y))

record HaarFeaturedLinearTransformer : Set where
  constructor haarFeaturedLinearTransformer
  field
    qProjection kProjection vProjection : Int8 → Int8
open HaarFeaturedLinearTransformer public

haarAccumulator-id : HaarAccumulator
haarAccumulator-id = zero8 , zero8

haarAccumulator-op :
  HaarAccumulator → HaarAccumulator → HaarAccumulator
haarAccumulator-op (a₁ , b₁) (a₂ , b₂) =
  int8Add a₁ a₂ , int8Add b₁ b₂

haarAccumulator-op-assoc :
  ∀ x y z →
  haarAccumulator-op
    (haarAccumulator-op x y)
    z
  ＝
  haarAccumulator-op
    x
    (haarAccumulator-op y z)
haarAccumulator-op-assoc
  (a₁ , b₁)
  (a₂ , b₂)
  (a₃ , b₃) =
  cong₂ _,_
    (int8+-assoc a₁ a₂ a₃)
    (int8+-assoc b₁ b₂ b₃)

haarAccumulator-op-idˡ :
  ∀ x →
  haarAccumulator-op haarAccumulator-id x ＝ x
haarAccumulator-op-idˡ (a , b) =
  cong₂ _,_
    (int8+-idˡ a)
    (int8+-idˡ b)

haarAccumulator-op-idʳ :
  ∀ x →
  haarAccumulator-op x haarAccumulator-id ＝ x
haarAccumulator-op-idʳ (a , b) =
  cong₂ _,_
    (int8+-idʳ a)
    (int8+-idʳ b)

haarKeyValueContribution :
  HaarFeaturedLinearTransformer →
  Int8 →
  HaarAccumulator
haarKeyValueContribution T x =
  let (kp , kn) =
        canonicalHaarFeature
          (kProjection T x)
      v = vProjection T x
  in int8Mul kp v , int8Mul kn v

haarAccumulatorStep :
  HaarFeaturedLinearTransformer →
  HaarAccumulator →
  Int8 →
  HaarAccumulator
haarAccumulatorStep T s x =
  haarAccumulator-op s
    (haarKeyValueContribution T x)

haarQueryRead :
  HaarFeaturedLinearTransformer →
  HaarAccumulator →
  Int8 →
  Int8
haarQueryRead T (sp , sn) x =
  let (qp , qn) =
        canonicalHaarFeature
          (qProjection T x)
  in int8Add
       (int8Mul qp sp)
       (int8Mul qn sn)

haarLinearTransform :
  HaarFeaturedLinearTransformer →
  HaarAccumulator →
  List Int8 →
  List Int8
haarLinearTransform T s₀ [] = []
haarLinearTransform T s₀ (x ∷ xs) =
  let s₁ = haarAccumulatorStep T s₀ x
  in haarQueryRead T s₁ x ∷
     haarLinearTransform T s₁ xs

haarLinearTransform-step-law :
  ∀ T s x →
  haarAccumulatorStep T s x ＝
  haarAccumulator-op s
    (haarKeyValueContribution T x)
haarLinearTransform-step-law T s x = refl

haarLinearTransform-associative-prefix :
  ∀ T s x y →
  haarAccumulatorStep T
    (haarAccumulatorStep T s x)
    y
  ＝
  haarAccumulator-op
    (haarAccumulatorStep T s x)
    (haarKeyValueContribution T y)
haarLinearTransform-associative-prefix T s x y = refl

canonicalHaarFeaturedTransformer :
  HaarFeaturedLinearTransformer
canonicalHaarFeaturedTransformer =
  haarFeaturedLinearTransformer
    identityActivation8
    identityActivation8
    identityActivation8

canonicalHaarFeaturedLinearScan :
  HaarAccumulator →
  List Int8 →
  List Int8
canonicalHaarFeaturedLinearScan =
  haarLinearTransform canonicalHaarFeaturedTransformer


record FullLearnerState (A : Set) : Set₁ where
  constructor fullLearnerState
  field
    watkins : WatkinsState A
    gru : GRUState
    optimizer : F4IntUState
    lcbCounts : LCBCountState A
    qLogControl : SignedQLogControl
    qLogValue : Dyadic
    haarAccumulator : HaarAccumulator
open FullLearnerState public

record FullLearnerKernel (A : Set) : Set₁ where
  constructor mkFullLearnerKernel
  field
    actionSpaceK : ActionSpace A
    watkinsKernel : WatkinsKernel A
    optimizerKernel : F4IntUKernel
    lcbKernel : LCBCountKernel
open FullLearnerKernel public

CanonicalFullLearnerState : Set₁
CanonicalFullLearnerState = FullLearnerState 𝟙

CanonicalFullLearnerKernel : Set₁
CanonicalFullLearnerKernel = FullLearnerKernel 𝟙

canonicalPolicy : ∀ {A : Set} → FullLearnerKernel A → FullLearnerState A → ℕ
canonicalPolicy K s = sparsemaxPolicy (actionSpaceK K) (lcbScore (lcbKernel K) (lcbCounts s) (critic (watkins s))) (valuesCount (lcbCounts s))

canonicalPolicyWeight : ∀ {A : Set} → FullLearnerKernel A → FullLearnerState A → SparseWeight
canonicalPolicyWeight K s = sparsemaxWeight (actionSpaceK K) (lcbScore (lcbKernel K) (lcbCounts s) (critic (watkins s))) (valuesCount (lcbCounts s)) (canonicalPolicy K s)

canonicalPolicyWeightCode : ∀ {A : Set} → FullLearnerKernel A → FullLearnerState A → Int8

BehaviorPolicy : Set
BehaviorPolicy = ℕ → SparseWeight

canonicalBehaviorPolicy :
  ∀ {A : Set} →
  FullLearnerKernel A →
  FullLearnerState A →
  BehaviorPolicy
canonicalBehaviorPolicy K s a =
  sparsemaxWeight
    (actionSpaceK K)
    (lcbScore
      (lcbKernel K)
      (lcbCounts s)
      (critic (watkins s)))
    (valuesCount (lcbCounts s))
    a

canonicalBehaviorAction :
  ∀ {A : Set} →
  FullLearnerKernel A →
  FullLearnerState A →
  ℕ
canonicalBehaviorAction K s = canonicalPolicy K s

canonicalBehaviorAction-law :
  ∀ {A : Set}
  (K : FullLearnerKernel A)
  (s : FullLearnerState A) →
  canonicalBehaviorAction K s ＝ canonicalPolicy K s
canonicalBehaviorAction-law K s = refl

canonicalPolicyWeightCode K s = int8OfNat (numerator (canonicalPolicyWeight K s))

HardSparse : ∀ {A : Set} → FullLearnerKernel A → FullLearnerState A → Set
HardSparse {A} K s =
  ∀ {a : ℕ} →
  a ≠ canonicalPolicy K s →
  numerator (sparsemaxWeight (actionSpaceK K) (lcbScore (lcbKernel K) (lcbCounts s) (critic (watkins s))) (valuesCount (lcbCounts s)) a) ＝ zero

SoftSparseBounded : ∀ {A : Set} →
  FullLearnerKernel A →
  FullLearnerState A →
  ℕ →
  Set
SoftSparseBounded {A} K s epsilon =
  ∀ {a : ℕ} →
  a ≠ canonicalPolicy K s →
  numerator
    (sparsemaxWeight
      (actionSpaceK K)
      (lcbScore (lcbKernel K) (lcbCounts s) (critic (watkins s)))
      (valuesCount (lcbCounts s))
      a)
  ≤ epsilon

hardSparse-to-softSparse-zero :
  ∀ {A}
  (K : FullLearnerKernel A)
  (s : FullLearnerState A) →
  HardSparse K s →
  SoftSparseBounded K s zero
hardSparse-to-softSparse-zero K s h {a} distinct =
  transport (λ n → n ≤ zero)
    (sym (h distinct))
    (zero-least zero)

softSparse-zero-to-hardSparse :
  ∀ {A}
  (K : FullLearnerKernel A)
  (s : FullLearnerState A) →
  SoftSparseBounded K s zero →
  HardSparse K s
softSparse-zero-to-hardSparse K s h {a} distinct =
  zero-least'' _ (h distinct)

replaceOptimizer : ∀ {A} → FullLearnerState A → F4IntUState → FullLearnerState A
replaceOptimizer s o = fullLearnerState (watkins s) (gru s) o
  (lcbCounts s) (qLogControl s) (qLogValue s) (haarAccumulator s)

canonicalPolicy-optimizer-invariant :
  ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) (o : F4IntUState) →
  canonicalPolicy K (replaceOptimizer s o) ＝ canonicalPolicy K s
canonicalPolicy-optimizer-invariant K s o = refl

maxCriticValueList : List Int8 → Int8
maxCriticValueList [] = zero8
maxCriticValueList (x ∷ xs) with compareInt8 x (maxCriticValueList xs)
... | less = maxCriticValueList xs
... | equal = maxCriticValueList xs
... | greater = x

maxCriticValue8 : ∀ {A : Set} → ActionSpace A → CriticState A → Int8
maxCriticValue8 K q = maxCriticValueList (map (λ a → values q a) (candidates K))

canonicalQLogBias : ∀ {A} → FullLearnerKernel A → FullLearnerState A → Int8
canonicalQLogBias K s = qLog2Bias8 (canonicalPolicyWeightCode K s)

canonicalReward8 : ∀ {A} → FullLearnerKernel A → FullLearnerState A → Int8
canonicalReward8 K s = canonicalPolicyWeightCode K s

canonicalDiscount8 : Int8
canonicalDiscount8 = one8

canonicalGRUFeedback : ∀ {A} → FullLearnerState A → Int8
canonicalGRUFeedback s = hiddenState (gru s)

canonicalF4L2Feedback : ∀ {A} → FullLearnerKernel A → FullLearnerState A → Int8
canonicalF4L2Feedback K s =
  int8Add
    (f4ThetaFull (optimizer s))
    (l2Correction (globalL2 (optimizerKernel K)))

canonicalQLogControlFeedback : ∀ {A} → FullLearnerState A → Int8
canonicalQLogControlFeedback s = coefficient (qLogControl s)

canonicalQLogValueFeedback : ∀ {A} → FullLearnerState A → Int8
canonicalQLogValueFeedback s = dyadicCode (qLogValue s)

canonicalEndogenousFeedback : ∀ {A} → FullLearnerKernel A → FullLearnerState A → Int8
canonicalEndogenousFeedback K s =
  int8Add
    (canonicalGRUFeedback s)
    (int8Add
        (canonicalF4L2Feedback K s)
        (int8Add
          (canonicalQLogControlFeedback s)
          (canonicalQLogValueFeedback s)))

canonicalWatkinsTarget : ∀ {A} → FullLearnerKernel A → FullLearnerState A → Int8
canonicalWatkinsTarget K s =
  int8Add
    (int8Add
      (int8Add (canonicalReward8 K s) (canonicalQLogBias K s))
      (int8Mul canonicalDiscount8 (maxCriticValue8 (actionSpaceK K) (critic (watkins s)))))
    (canonicalEndogenousFeedback K s)

canonicalWatkinsTarget-law : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) →
  canonicalWatkinsTarget K s ＝
  int8Add
    (int8Add
      (int8Add (canonicalReward8 K s) (canonicalQLogBias K s))
      (int8Mul canonicalDiscount8 (maxCriticValue8 (actionSpaceK K) (critic (watkins s)))))
    (canonicalEndogenousFeedback K s)
canonicalWatkinsTarget-law K s = refl

canonicalQLogControlStep : ∀ {A} → FullLearnerKernel A → FullLearnerState A → SignedQLogControl
canonicalQLogControlStep K s =
  signedQLogControl negativeAlpha8 (canonicalQLogBias K s)

canonicalSignal : ∀ {A} → FullLearnerKernel A → FullLearnerState A → Int8
canonicalSignal = canonicalWatkinsTarget

canonicalSignal-watkins-target : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) →
  canonicalSignal K s ＝ canonicalWatkinsTarget K s
canonicalSignal-watkins-target K s = refl

canonicalWatkinsStep : ∀ {A} → FullLearnerKernel A → FullLearnerState A → WatkinsState A
canonicalWatkinsStep K s =
  watkinsStep (watkinsKernel K)
  (watkinsState (critic (watkins s)) (canonicalSignal K s) (trace (watkins s)))

canonicalHaarAccumulatorStep :
  ∀ {A} →
  FullLearnerKernel A →
  FullLearnerState A →
  HaarAccumulator
canonicalHaarAccumulatorStep K s =
  haarAccumulatorStep
    canonicalHaarFeaturedTransformer
    (haarAccumulator s)
    (canonicalSignal K s)

canonicalHaarRecurrentInput :
  ∀ {A} →
  FullLearnerKernel A →
  FullLearnerState A →
  Int8
canonicalHaarRecurrentInput K s =
  haarQueryRead
    canonicalHaarFeaturedTransformer
    (canonicalHaarAccumulatorStep K s)
    (canonicalSignal K s)

canonicalGRUStep : ∀ {A} → FullLearnerKernel A → FullLearnerState A → GRUState
canonicalGRUStep K s =
  gruStep
    (gru s)
    (canonicalHaarRecurrentInput K s)

canonicalPersistentGRUPreservation : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) →
  persistentGRU (canonicalGRUStep K s) ＝ persistentGRU (gru s)
canonicalPersistentGRUPreservation K s =
  persistent-preservation (gru s)
    (canonicalSignal K s)

canonicalRecurrentInput-law : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) →
  canonicalGRUStep K s ＝
  gruStep (gru s)
    (canonicalHaarRecurrentInput K s)
canonicalRecurrentInput-law K s = refl

canonicalOptimizerStep : ∀ {A} → FullLearnerKernel A → FullLearnerState A → F4IntUState
canonicalOptimizerStep K s = f4ThetaStep (optimizerKernel K) (optimizer s) (canonicalSignal K s)

canonicalOptimizerStep-qMunchausen-L2 : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) →
  canonicalOptimizerStep K s ＝
  f4ThetaStep
    (optimizerKernel K)
    (optimizer s)
    (canonicalWatkinsTarget K s)
canonicalOptimizerStep-qMunchausen-L2 K s = refl

canonicalCountStep : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) → LCBCountState A
canonicalCountStep K s = updateLCBCount (canonicalPolicy K s) (lcbCounts s)

canonicalQLogStep : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) → Dyadic
canonicalQLogStep K s = qLog8 (canonicalPolicyWeightCode K s)

canonicalFullStep : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) → FullLearnerState A
canonicalFullStep K s =
  fullLearnerState (canonicalWatkinsStep K s)
  (canonicalGRUStep K s)
  (canonicalOptimizerStep K s)
  (canonicalCountStep K s)
  (canonicalQLogControlStep K s)
  (canonicalQLogStep K s)
  (canonicalHaarAccumulatorStep K s)

canonicalFullStep-watkins : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) → watkins (canonicalFullStep K s) ＝ canonicalWatkinsStep K s
canonicalFullStep-watkins K s = refl

canonicalFullStep-gru : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) → gru (canonicalFullStep K s) ＝ canonicalGRUStep K s
canonicalFullStep-gru K s = refl

canonicalFullStep-optimizer : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) → optimizer (canonicalFullStep K s) ＝ canonicalOptimizerStep K s
canonicalFullStep-optimizer K s = refl

canonicalFullStep-counts : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) → lcbCounts (canonicalFullStep K s) ＝ canonicalCountStep K s
canonicalFullStep-counts K s = refl

canonicalFullStep-qLog : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) → qLogValue (canonicalFullStep K s) ＝ canonicalQLogStep K s
canonicalFullStep-qLog K s = refl

canonicalFullStep-qLogControl : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) → qLogControl (canonicalFullStep K s) ＝ canonicalQLogControlStep K s
canonicalFullStep-qLogControl K s = refl

canonicalTotalCountStep : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) → totalCount (lcbCounts (canonicalFullStep K s)) ＝ succ (totalCount (lcbCounts s))
canonicalTotalCountStep K s = refl

canonicalNoFixedPoint :
  ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) →
  canonicalFullStep K s ≠ s
canonicalNoFixedPoint K s eq =
  plus-succ-not-self (totalCount (lcbCounts s)) zero
    (trans (plus-succ (totalCount (lcbCounts s)) zero)
      (trans (ap succ (plus-zero (totalCount (lcbCounts s))))
        (trans (sym (canonicalTotalCountStep K s))
          (ap (λ t → totalCount (lcbCounts t)) eq))))

iterateCanonical : ∀ {A} → FullLearnerKernel A → ℕ → FullLearnerState A → FullLearnerState A
iterateCanonical K zero s = s
iterateCanonical K (succ n) s = canonicalFullStep K (iterateCanonical K n s)

canonicalTotalCountAfter :
  ∀ {A} (K : FullLearnerKernel A) (n : ℕ) (s : FullLearnerState A) →
  totalCount (lcbCounts (iterateCanonical K n s)) ＝
  totalCount (lcbCounts s) + n
canonicalTotalCountAfter K zero s = sym (plus-zero (totalCount (lcbCounts s)))
canonicalTotalCountAfter K (succ n) s =
  trans
    (canonicalTotalCountStep K (iterateCanonical K n s))
    (trans
      (ap succ (canonicalTotalCountAfter K n s))
      (sym (plus-succ (totalCount (lcbCounts s)) n)))

canonicalAperiodic : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) (n : ℕ) → iterateCanonical K (succ n) s ≠ s
canonicalAperiodic K s n cyc = plus-succ-not-self (totalCount (lcbCounts s)) n
  (trans
    (sym (canonicalTotalCountAfter K (succ n) s))
    (ap (λ t → totalCount (lcbCounts t)) cyc))

canonicalOrbitNonFixed : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) (n : ℕ) → iterateCanonical K n s ≠ canonicalFullStep K (iterateCanonical K n s)
canonicalOrbitNonFixed K s n eq =
  canonicalNoFixedPoint K (iterateCanonical K n s) (eq ⁻¹)

canonicalNoNontrivialFiniteCycle : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) (n : ℕ) → iterateCanonical K (succ n) s ＝ s → 𝟘
canonicalNoNontrivialFiniteCycle K s n cyc = canonicalAperiodic K s n cyc

canonicalTotalCountIterate2 : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) → totalCount (lcbCounts (iterateCanonical K 2 s)) ＝ succ (succ (totalCount (lcbCounts s)))
canonicalTotalCountIterate2 K s = refl

canonicalNoCountedTwoCycle : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) → iterateCanonical K 2 s ＝ s → 𝟘
canonicalNoCountedTwoCycle K s cyc = succ-succ-not-self (totalCount (lcbCounts s))
  (trans (sym (canonicalTotalCountIterate2 K s))
    (ap (λ t → totalCount (lcbCounts t)) cyc))

temperatureCodeLaw : sparsemaxTemperature ＝ 16
temperatureCodeLaw = refl

pessimisticInit : Int8
pessimisticInit = int8OfNat 128

pessimisticCritic : ∀ {A} → CriticState A
pessimisticCritic {A} = criticState (λ _ → pessimisticInit)

pessimisticCritic-law : ∀ {A} (i : ℕ) → values (pessimisticCritic {A = A}) i ＝ pessimisticInit
pessimisticCritic-law {A = A} i = refl

canonicalPersistent : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) → persistentGRU (canonicalGRUStep K s) ＝ persistentGRU (gru s)
canonicalPersistent = canonicalPersistentGRUPreservation

CanonicalToken : Set
CanonicalToken = Int

CanonicalTokenSequence : Set
CanonicalTokenSequence = List CanonicalToken

canonicalTokenEncode : CanonicalToken → Int8
canonicalTokenEncode = int8

canonicalTokenEncodeList : CanonicalTokenSequence → List Int8
canonicalTokenEncodeList = map canonicalTokenEncode

canonicalTokenStep : GRUState → CanonicalToken → GRUState
canonicalTokenStep s t = gruStep s (canonicalTokenEncode t)

canonicalTokenRecurrentNetwork :
  RecurrentNetwork GRUState CanonicalToken
canonicalTokenRecurrentNetwork =
  recurrentNetwork canonicalTokenStep

recurrentListState :
  ∀ {State Input : Set} →
  RecurrentNetwork State Input →
  List Input →
  State →
  State
recurrentListState R [] s = s
recurrentListState R (x ∷ xs) s =
  recurrentListState R xs (runNetwork R s x)

canonicalTokenListState :
  CanonicalTokenSequence →
  GRUState →
  GRUState
canonicalTokenListState [] s = s
canonicalTokenListState (t ∷ ts) s =
  canonicalTokenListState ts (canonicalTokenStep s t)

CanonicalTokenLogitVector : Set
CanonicalTokenLogitVector = CanonicalToken → Int8

record CanonicalTokenLanguageModelKernel : Set₁ where
  constructor canonicalTokenLanguageModelKernel
  field
    logits : GRUState → CanonicalTokenLogitVector
open CanonicalTokenLanguageModelKernel public

canonicalTokenLogitTrace :
  CanonicalTokenLanguageModelKernel →
  CanonicalTokenSequence →
  GRUState →
  List CanonicalTokenLogitVector
canonicalTokenLogitTrace K [] s = []
canonicalTokenLogitTrace K (t ∷ ts) s =
  logits K s ∷
  canonicalTokenLogitTrace K ts (canonicalTokenStep s t)



