{-# OPTIONS
--safe
--guardedness
--lossy-unification
--syntactic-equality=1
--no-eta-equality
--with-K
--exact-split
#-}

module TheoremsMonolith where


open import Agda.Builtin.Nat public
open import Agda.Builtin.Int public
open import Agda.Builtin.Bool public
open import Agda.Builtin.List public
open import Agda.Builtin.Maybe public
open import Agda.Builtin.Sigma public
open import Agda.Builtin.Equality public
-- No standard library dependency: define the empty type locally.
data ⊥ : Set where

------------------------------------------------------------------------
-- Small utilities
------------------------------------------------------------------------

infixr 3 _×_
infixr 9 _∘ᶠ_

¬_ : Set → Set
¬ P = P → ⊥

record _×_ (A B : Set) : Set where
  no-eta-equality
  pattern
  constructor pair
  field
    fst : A
    snd : B
open _×_ public

cong : {A B : Set} {x y : A} (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : {A B C : Set} (f : A → B → C) {a a′ : A} {b b′ : B} →
        a ≡ a′ → b ≡ b′ → f a b ≡ f a′ b′
cong₂ f refl refl = refl

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q

idᶠ : {A : Set} → A → A
idᶠ x = x

_∘ᶠ_ : {A B C : Set} → (B → C) → (A → B) → A → C
(g ∘ᶠ f) x = g (f x)

record Iso (A B : Set) : Set where
  constructor iso
  field
    to       : A → B
    from     : B → A
    from-to  : (x : A) → from (to x) ≡ x
    to-from  : (y : B) → to (from y) ≡ y
open Iso public

infixr 5 _∷ᵥ_

data Vec (A : Set) : Nat → Set where
  []ᵥ : Vec A zero
  _∷ᵥ_ : {n : Nat} → A → Vec A n → Vec A (suc n)

replicateVec : {A : Set} → (n : Nat) → A → Vec A n
replicateVec zero x = []ᵥ
replicateVec (suc n) x = x ∷ᵥ replicateVec n x

tabulateVec : {A : Set} → (n : Nat) → (Nat → A) → Vec A n
tabulateVec zero f = []ᵥ
tabulateVec (suc n) f = f zero ∷ᵥ tabulateVec n (λ i → f (suc i))

lookupVecOr : {A : Set} {n : Nat} → A → Nat → Vec A n → A
lookupVecOr fallback zero []ᵥ = fallback
lookupVecOr fallback zero (x ∷ᵥ xs) = x
lookupVecOr fallback (suc i) []ᵥ = fallback
lookupVecOr fallback (suc i) (x ∷ᵥ xs) = lookupVecOr fallback i xs

------------------------------------------------------------------------
-- SIGNED INTEGER CORE
--
-- Agda.Builtin.Int supplies the canonical signed representation:
--   pos n    represents n
--   negsuc n represents -(n + 1)
--
-- Arithmetic below stays in mathematical Nat/Int.  No machine-cell
-- bound or floating-point conversion enters this layer.
------------------------------------------------------------------------

module IntegerArithmetic where

  open import Agda.Builtin.Int using (Int; pos; negsuc)

  intFromNat : Nat → Int
  intFromNat = pos

  intNegate : Int → Int
  intNegate (pos zero) = pos zero
  intNegate (pos (suc n)) = negsuc n
  intNegate (negsuc n) = pos (suc n)

  intAdd : Int → Int → Int
  intAdd (pos m) (pos n) =
    pos (Agda.Builtin.Nat._+_ m n)
  intAdd (pos m) (negsuc n) with Agda.Builtin.Nat._<_ m (suc n)
  ... | true = negsuc (Agda.Builtin.Nat._-_ n m)
  ... | false = pos (Agda.Builtin.Nat._-_ m (suc n))
  intAdd (negsuc m) (pos n) with Agda.Builtin.Nat._<_ n (suc m)
  ... | true = negsuc (Agda.Builtin.Nat._-_ m n)
  ... | false = pos (Agda.Builtin.Nat._-_ n (suc m))
  intAdd (negsuc m) (negsuc n) =
    negsuc (suc (Agda.Builtin.Nat._+_ m n))

  intSubtract : Int → Int → Int
  intSubtract x y = intAdd x (intNegate y)

  intMultiply : Int → Int → Int
  intMultiply (pos m) (pos n) =
    pos (Agda.Builtin.Nat._*_ m n)
  intMultiply (pos zero) (negsuc n) = pos zero
  intMultiply (pos (suc m)) (negsuc n) =
    negsuc
      (Agda.Builtin.Nat._-_
        (Agda.Builtin.Nat._*_ (suc m) (suc n))
        (suc zero))
  intMultiply (negsuc m) (pos zero) = pos zero
  intMultiply (negsuc m) (pos (suc n)) =
    negsuc
      (Agda.Builtin.Nat._-_
        (Agda.Builtin.Nat._*_ (suc m) (suc n))
        (suc zero))
  intMultiply (negsuc m) (negsuc n) =
    pos (Agda.Builtin.Nat._*_ (suc m) (suc n))

  intEqual : Int → Int → Bool
  intEqual (pos m) (pos n) = Agda.Builtin.Nat._==_ m n
  intEqual (negsuc m) (negsuc n) = Agda.Builtin.Nat._==_ m n
  intEqual (pos m) (negsuc n) = false
  intEqual (negsuc m) (pos n) = false

  intLessThan : Int → Int → Bool
  intLessThan (pos m) (pos n) = Agda.Builtin.Nat._<_ m n
  intLessThan (pos m) (negsuc n) = false
  intLessThan (negsuc m) (pos n) = true
  intLessThan (negsuc m) (negsuc n) = Agda.Builtin.Nat._<_ n m

  intNegate-involutive : (x : Int) → intNegate (intNegate x) ≡ x
  intNegate-involutive (pos zero) = refl
  intNegate-involutive (pos (suc n)) = refl
  intNegate-involutive (negsuc n) = refl

  intNegate-fromNat-suc :
    (n : Nat) → intNegate (intFromNat (suc n)) ≡ negsuc n
  intNegate-fromNat-suc n = refl

  intFromNat-add :
    (m n : Nat) →
    intFromNat (Agda.Builtin.Nat._+_ m n) ≡
    intAdd (intFromNat m) (intFromNat n)
  intFromNat-add m n = refl

  intFromNat-multiply :
    (m n : Nat) →
    intFromNat (Agda.Builtin.Nat._*_ m n) ≡
    intMultiply (intFromNat m) (intFromNat n)
  intFromNat-multiply m n = refl

  intAdd-example-positive :
    intAdd (pos 5) (negsuc 2) ≡ pos 2
  intAdd-example-positive = refl

  intAdd-example-negative :
    intAdd (pos 1) (negsuc 2) ≡ negsuc 1
  intAdd-example-negative = refl

  intMultiply-example-negative :
    intMultiply (pos 2) (negsuc 2) ≡ negsuc 5
  intMultiply-example-negative = refl

  intMultiply-example-positive :
    intMultiply (negsuc 1) (negsuc 2) ≡ pos 6
  intMultiply-example-positive = refl

open IntegerArithmetic public

------------------------------------------------------------------------
-- FINITE LIST COMPUTATION
--
-- Auxiliary constructive witness; separate from the six foundational
-- packages and the Laurent MALLP calculus. Finite coordinates are represented
-- by ordinary Lists and Nat labels.
-- No bounded-index container is introduced. Finite prefixes
-- are enumerated by tabulateList; lookupPrefix records bounded lookup as
-- Maybe, while lookupListOr supplies an explicit default for sparse tails.
------------------------------------------------------------------------


mapList : {A B : Set} → (A → B) → List A → List B
mapList f [] = []
mapList f (x ∷ xs) = f x ∷ mapList f xs

replicateList : {A : Set} → Nat → A → List A
replicateList zero x = []
replicateList (suc n) x = x ∷ replicateList n x

tabulateList : {A : Set} → (n : Nat) → (Nat → A) → List A
tabulateList zero f = []
tabulateList (suc n) f = f zero ∷ tabulateList n (λ i → f (suc i))

lookupPrefix : {A : Set} → (n : Nat) → List A →
               (i : Nat) → (i < n) ≡ true → Maybe A
lookupPrefix zero xs i ()
lookupPrefix (suc n) [] i bound = nothing
lookupPrefix (suc n) (x ∷ xs) zero refl = just x
lookupPrefix (suc n) (x ∷ xs) (suc i) bound =
  lookupPrefix n xs i bound

lookupListOr : {A : Set} → A → Nat → List A → A
lookupListOr fallback zero [] = fallback
lookupListOr fallback zero (x ∷ xs) = x
lookupListOr fallback (suc i) [] = fallback
lookupListOr fallback (suc i) (x ∷ xs) = lookupListOr fallback i xs

------------------------------------------------------------------------
-- FINITE LIST COMPUTATION: AUXILIARY CONSTRUCTIVE WITNESS
--
-- This theorem remains available to finite-prefix code, separate from the
-- six foundational packages and Laurent MALLP.
------------------------------------------------------------------------

module FiniteListComputation where

  lookup-tabulate :
    {A : Set} → (n : Nat) → (f : Nat → A) →
    (i : Nat) → (bound : (i < n) ≡ true) →
    lookupPrefix n (tabulateList n f) i bound ≡ just (f i)
  lookup-tabulate zero f i ()
  lookup-tabulate (suc n) f zero refl = refl
  lookup-tabulate (suc n) f (suc i) bound =
    lookup-tabulate n (λ j → f (suc j)) i bound

open FiniteListComputation public

------------------------------------------------------------------------
-- CONATURALS: CONSTRUCTIVE COINDUCTIVE TIME HORIZONS
------------------------------------------------------------------------

open import Agda.Builtin.Coinduction public

data Conat : Set where
  zero∞ : Conat
  suc∞ : ∞ Conat → Conat

observeConat : Conat → Maybe Conat
observeConat zero∞ = nothing
observeConat (suc∞ predecessor) = just (♭ predecessor)

infinity : Conat
infinity = suc∞ (♯ infinity)

fromNat : Nat → Conat
fromNat zero = zero∞
fromNat (suc n) = suc∞ (♯ (fromNat n))

-- A bounded observation: after k observations, an infinite value is
-- represented by the cutoff k.  This always terminates by recursion on k.
finiteApproximation : Nat → Conat → Nat
finiteApproximation zero n = zero
finiteApproximation (suc k) n with observeConat n
... | nothing = zero
... | just predecessor = suc (finiteApproximation k predecessor)

finiteApproximation-fromNat :
  (n : Nat) → finiteApproximation n (fromNat n) ≡ n
finiteApproximation-fromNat zero = refl
finiteApproximation-fromNat (suc n) =
  cong suc (finiteApproximation-fromNat n)

finiteApproximation-infinity :
  (n : Nat) → finiteApproximation n infinity ≡ n
finiteApproximation-infinity zero = refl
finiteApproximation-infinity (suc n) =
  cong suc (finiteApproximation-infinity n)

-- Addition is productive: the left argument is inspected once, and every
-- recursive call is guarded under the successor observation constructor.
_+∞_ : Conat → Conat → Conat
zero∞ +∞ b = b
suc∞ predecessor +∞ b = suc∞ (♯ (♭ predecessor +∞ b))

------------------------------------------------------------------------
-- CONATURAL STREAMS AND A NEGATIVE OBSERVATION VIEW
------------------------------------------------------------------------

-- A stream whose length is a conatural.  Its finite prefixes are always
-- computable; an infinite horizon is observed one constructor at a time.
data ConatStream (A : Set) : Set where
  emptyConatStream : ConatStream A
  consConatStream : A → ∞ (ConatStream A) → ConatStream A

observeStream : {A : Set} → ConatStream A → Maybe (A × ConatStream A)
observeStream emptyConatStream = nothing
observeStream (consConatStream value rest) = just (pair value (♭ rest))

iterateConat : {A : Set} → (A → A) → Conat → A → ConatStream A
iterateConat step horizon state with observeConat horizon
... | nothing = emptyConatStream
... | just remaining =
      consConatStream state (♯ (iterateConat step remaining (step state)))

mapConatStream : {A B : Set} → (A → B) → ConatStream A → ConatStream B
mapConatStream f emptyConatStream = emptyConatStream
mapConatStream f (consConatStream value rest) =
  consConatStream (f value) (♯ (mapConatStream f (♭ rest)))

-- The bound, rather than the stream, controls recursion.  This evaluator is
-- total even for an infinite stream and is the executable observation API.
foldConatPrefix : {A R : Set} → (A → R → R) → R → Nat → ConatStream A → R
foldConatPrefix step initial zero stream = initial
foldConatPrefix step initial (suc n) stream with observeStream stream
... | nothing = initial
... | just (pair value rest) =
      step value (foldConatPrefix step initial n rest)

------------------------------------------------------------------------
-- CODYADIC EXACT REAL CODES
------------------------------------------------------------------------

-- A digit denotes -1, 0, or +1.  A code denotes
--
--   2 ^ binaryShift * Σ (digit[n] * 2 ^ (-(n + 1))).
--
-- The digit stream is genuinely infinite: its codata has a digit and a
-- delayed tail, never an end marker.  binaryShift is a finite signed
-- integer; Conat controls observation precision, never the real scale.
data SignedBinaryDigit : Set where
  negativeDigit zeroDigit positiveDigit : SignedBinaryDigit

data CodyadicDigitStream : Set where
  codyadicDigitStep : SignedBinaryDigit → ∞ CodyadicDigitStream → CodyadicDigitStream

codyadicHead : CodyadicDigitStream → SignedBinaryDigit
codyadicHead (codyadicDigitStep head tail) = head

codyadicTail : CodyadicDigitStream → CodyadicDigitStream
codyadicTail (codyadicDigitStep head tail) = ♭ tail

record Codyadic : Set where
  constructor codyadic
  field
    codyadicBinaryShift : Int
    codyadicMantissa : CodyadicDigitStream
open Codyadic public

-- The unbounded view is productive at every observation.
codyadicDigitObservations :
  CodyadicDigitStream → ConatStream SignedBinaryDigit
codyadicDigitObservations digits =
  consConatStream
    (codyadicHead digits)
    (♯ (codyadicDigitObservations (codyadicTail digits)))

-- A Conat requests a finite or infinite prefix without truncating the
-- underlying Codyadic value.
codyadicDigitPrefix :
  Conat → CodyadicDigitStream → ConatStream SignedBinaryDigit
codyadicDigitPrefix horizon digits with observeConat horizon
... | nothing = emptyConatStream
... | just rest =
      consConatStream
        (codyadicHead digits)
        (♯ (codyadicDigitPrefix rest (codyadicTail digits)))

codyadicObservations : Codyadic → ConatStream SignedBinaryDigit
codyadicObservations value =
  codyadicDigitObservations (codyadicMantissa value)

------------------------------------------------------------------------
-- CONSTRUCTIVE CODYADIC SETOID-FIELD CONTRACT
------------------------------------------------------------------------

infixr 3 _⊎ᶜ_
data _⊎ᶜ_ (A B : Set) : Set where
  codyadicLeft : A → A ⊎ᶜ B
  codyadicRight : B → A ⊎ᶜ B

-- Signed-digit expansions are redundant, so structural stream equality
-- is not the real equality.  A concrete implementation supplies semantic
-- setoid equality, productive operations, and all ring/field laws.
--
-- Division is constructive only with an apartness witness from zero.
-- A proof of mere negated equality does not supply a computable lower
-- bound on the denominator's magnitude.
record CodyadicFieldInterface : Set₁ where
  field
    _≈ᶜ_ : Codyadic → Codyadic → Set
    _#ᶜ_ : Codyadic → Codyadic → Set
    _+ᶜ_ _*ᶜ_ : Codyadic → Codyadic → Codyadic

  infix 4 _≈ᶜ_ _#ᶜ_
  infixl 6 _+ᶜ_
  infixl 7 _*ᶜ_

  field
    zeroᶜ oneᶜ : Codyadic
    negateᶜ : Codyadic → Codyadic
    reciprocalᶜ : (value : Codyadic) → value #ᶜ zeroᶜ → Codyadic

    ≈ᶜ-refl : (x : Codyadic) → x ≈ᶜ x
    ≈ᶜ-sym : {x y : Codyadic} → x ≈ᶜ y → y ≈ᶜ x
    ≈ᶜ-trans :
      {x y z : Codyadic} → x ≈ᶜ y → y ≈ᶜ z → x ≈ᶜ z

    +ᶜ-cong :
      {x x′ y y′ : Codyadic} →
      x ≈ᶜ x′ → y ≈ᶜ y′ → (x +ᶜ y) ≈ᶜ (x′ +ᶜ y′)
    *ᶜ-cong :
      {x x′ y y′ : Codyadic} →
      x ≈ᶜ x′ → y ≈ᶜ y′ → (x *ᶜ y) ≈ᶜ (x′ *ᶜ y′)
    negateᶜ-cong :
      {x y : Codyadic} → x ≈ᶜ y → negateᶜ x ≈ᶜ negateᶜ y

    +ᶜ-assoc :
      (x y z : Codyadic) →
      ((x +ᶜ y) +ᶜ z) ≈ᶜ (x +ᶜ (y +ᶜ z))
    +ᶜ-comm :
      (x y : Codyadic) → (x +ᶜ y) ≈ᶜ (y +ᶜ x)
    +ᶜ-zeroˡ : (x : Codyadic) → (zeroᶜ +ᶜ x) ≈ᶜ x
    +ᶜ-zeroʳ : (x : Codyadic) → (x +ᶜ zeroᶜ) ≈ᶜ x
    +ᶜ-inverseʳ :
      (x : Codyadic) → (x +ᶜ negateᶜ x) ≈ᶜ zeroᶜ

    *ᶜ-assoc :
      (x y z : Codyadic) →
      ((x *ᶜ y) *ᶜ z) ≈ᶜ (x *ᶜ (y *ᶜ z))
    *ᶜ-comm :
      (x y : Codyadic) → (x *ᶜ y) ≈ᶜ (y *ᶜ x)
    *ᶜ-oneˡ : (x : Codyadic) → (oneᶜ *ᶜ x) ≈ᶜ x
    *ᶜ-oneʳ : (x : Codyadic) → (x *ᶜ oneᶜ) ≈ᶜ x
    *ᶜ-zeroˡ : (x : Codyadic) → (zeroᶜ *ᶜ x) ≈ᶜ zeroᶜ
    *ᶜ-distribˡ :
      (x y z : Codyadic) →
      (x *ᶜ (y +ᶜ z)) ≈ᶜ ((x *ᶜ y) +ᶜ (x *ᶜ z))

    #ᶜ-irreflexive : (x : Codyadic) → ¬ (x #ᶜ x)
    #ᶜ-symmetric :
      {x y : Codyadic} → x #ᶜ y → y #ᶜ x
    #ᶜ-cotransitive :
      {x y z : Codyadic} →
      x #ᶜ z → (x #ᶜ y) ⊎ᶜ (y #ᶜ z)
    #ᶜ-separates :
      {x y : Codyadic} → x #ᶜ y → ¬ (x ≈ᶜ y)

    oneᶜ-apart-zeroᶜ : oneᶜ #ᶜ zeroᶜ
    reciprocalᶜ-left :
      (x : Codyadic) (apartFromZero : x #ᶜ zeroᶜ) →
      (reciprocalᶜ x apartFromZero *ᶜ x) ≈ᶜ oneᶜ
    reciprocalᶜ-right :
      (x : Codyadic) (apartFromZero : x #ᶜ zeroᶜ) →
      (x *ᶜ reciprocalᶜ x apartFromZero) ≈ᶜ oneᶜ
open CodyadicFieldInterface public

------------------------------------------------------------------------
-- MODULE 1: SIX FOUNDATIONAL PACKAGES AND LAURENT MALLP
------------------------------------------------------------------------

record RationalRingInterface : Set₂ where
  field
    Rational : Set
    0ℚ 1ℚ : Rational
    _+ℚ_ _-ℚ_ _*ℚ_ : Rational → Rational → Rational

    +ℚ-assoc : (a b c : Rational) →
               ((a +ℚ b) +ℚ c) ≡ (a +ℚ (b +ℚ c))
    +ℚ-comm : (a b : Rational) → (a +ℚ b) ≡ (b +ℚ a)
    +ℚ-zeroˡ : (a : Rational) → (0ℚ +ℚ a) ≡ a
    +ℚ-zeroʳ : (a : Rational) → (a +ℚ 0ℚ) ≡ a
    +ℚ-inverseʳ : (a : Rational) → (a +ℚ (0ℚ -ℚ a)) ≡ 0ℚ
    -ℚ-definition : (a b : Rational) →
                    (a -ℚ b) ≡ (a +ℚ (0ℚ -ℚ b))

    *ℚ-assoc : (a b c : Rational) →
               ((a *ℚ b) *ℚ c) ≡ (a *ℚ (b *ℚ c))
    *ℚ-comm : (a b : Rational) → (a *ℚ b) ≡ (b *ℚ a)
    *ℚ-oneˡ : (a : Rational) → (1ℚ *ℚ a) ≡ a
    *ℚ-oneʳ : (a : Rational) → (a *ℚ 1ℚ) ≡ a
    *ℚ-zeroˡ : (a : Rational) → (0ℚ *ℚ a) ≡ 0ℚ
    *ℚ-distribˡ : (a b c : Rational) →
                  (a *ℚ (b +ℚ c)) ≡ ((a *ℚ b) +ℚ (a *ℚ c))

module FiniteRationalSums (Q : RationalRingInterface) where
  open RationalRingInterface Q

  sumFinite : (n : Nat) → (Nat → Rational) → Rational
  sumFinite zero f = 0ℚ
  sumFinite (suc n) f = f zero +ℚ sumFinite n (λ i → f (suc i))

  sumFinite-cong :
    (n : Nat) (f g : Nat → Rational) →
    ((i : Nat) → f i ≡ g i) →
    sumFinite n f ≡ sumFinite n g
  sumFinite-cong zero f g pointwise = refl
  sumFinite-cong (suc n) f g pointwise =
    cong₂ _+ℚ_
      (pointwise zero)
      (sumFinite-cong n
        (λ i → f (suc i))
        (λ i → g (suc i))
        (λ i → pointwise (suc i)))

module RationalSED (Q : RationalRingInterface) where

  open RationalRingInterface Q

  ----------------------------------------------------------------------
  -- Four-vectors and Minkowski quadrance, signature (+---).
  ----------------------------------------------------------------------

  record Rational4Vector : Set where
    constructor r4
    field
      ct x y z : Rational
  open Rational4Vector public

  minkowskiQuadrance : Rational4Vector → Rational
  minkowskiQuadrance u =
    (((ct u *ℚ ct u) -ℚ (x u *ℚ x u)) -ℚ (y u *ℚ y u)) -ℚ (z u *ℚ z u)

  _+₄_ : Rational4Vector → Rational4Vector → Rational4Vector
  r4 t₁ x₁ y₁ z₁ +₄ r4 t₂ x₂ y₂ z₂ =
    r4 (t₁ +ℚ t₂) (x₁ +ℚ x₂) (y₁ +ℚ y₂) (z₁ +ℚ z₂)

  _-₄_ : Rational4Vector → Rational4Vector → Rational4Vector
  r4 t₁ x₁ y₁ z₁ -₄ r4 t₂ x₂ y₂ z₂ =
    r4 (t₁ -ℚ t₂) (x₁ -ℚ x₂) (y₁ -ℚ y₂) (z₁ -ℚ z₂)

  r4-cong : {t t′ x x′ y y′ z z′ : Rational} →
            t ≡ t′ → x ≡ x′ → y ≡ y′ → z ≡ z′ →
            r4 t x y z ≡ r4 t′ x′ y′ z′
  r4-cong refl refl refl refl = refl

  ----------------------------------------------------------------------
  -- Rational (ct,x)-plane Cayley boost.
  --
  -- For rational parameter a, the Cayley coefficients are
  --
  --   d = 4 - a²,  c = (4 + a²)/d,  s = 4a/d.
  --
  -- Cross-multiplied equations avoid introducing a partial division
  -- operation into the interface.  The Lorentz identity is retained as
  -- an explicit certificate to be derived from the ring laws.
  ----------------------------------------------------------------------

  fourℚ : Rational
  fourℚ = (1ℚ +ℚ 1ℚ) +ℚ (1ℚ +ℚ 1ℚ)

  record CertifiedCayleyPlaneBoost : Set₁ where
    field
      parameter denominator c s : Rational

      denominator-formula :
        denominator ≡ (fourℚ -ℚ (parameter *ℚ parameter))

      denominator-nonzero : ¬ (denominator ≡ 0ℚ)

      c-formula :
        (c *ℚ denominator) ≡ (fourℚ +ℚ (parameter *ℚ parameter))

      s-formula :
        (s *ℚ denominator) ≡ (fourℚ *ℚ parameter)

      lorentz-condition :
        ((c *ℚ c) -ℚ (s *ℚ s)) ≡ 1ℚ

      preservesQuadrance :
        (u : Rational4Vector) →
        minkowskiQuadrance
          (r4 ((c *ℚ ct u) +ℚ (s *ℚ x u))
              ((s *ℚ ct u) +ℚ (c *ℚ x u))
              (y u) (z u))
        ≡ minkowskiQuadrance u

  applyCayleyPlaneBoost :
    CertifiedCayleyPlaneBoost → Rational4Vector → Rational4Vector
  applyCayleyPlaneBoost B u =
    r4 ((CertifiedCayleyPlaneBoost.c B *ℚ ct u) +ℚ
        (CertifiedCayleyPlaneBoost.s B *ℚ x u))
       ((CertifiedCayleyPlaneBoost.s B *ℚ ct u) +ℚ
        (CertifiedCayleyPlaneBoost.c B *ℚ x u))
       (y u) (z u)

  ----------------------------------------------------------------------
  -- Momentum accounting without a free compensating harmonic term.
  --
  -- A transition records particle and field momentum before/after.  The
  -- conservation proposition is an obligation to prove from dynamics.
  ----------------------------------------------------------------------

  record MomentumSnapshot : Set where
    constructor snapshot
    field
      particleMomentum : Rational4Vector
      fieldMomentum    : Rational4Vector
  open MomentumSnapshot public

  totalMomentum : MomentumSnapshot → Rational4Vector
  totalMomentum s = particleMomentum s +₄ fieldMomentum s

  record MomentumTransition : Set where
    constructor transition
    field
      before after : MomentumSnapshot
  open MomentumTransition public

  MomentumConserved : MomentumTransition → Set
  MomentumConserved tr = totalMomentum (before tr) ≡ totalMomentum (after tr)

  -- The dynamics must construct this certificate.  No arbitrary harmonic
  -- vector is permitted to cancel a residual by definition.
  record ConservationCertificate (tr : MomentumTransition) : Set where
    field
      totalMomentumConservation : MomentumConserved tr

------------------------------------------------------------------------
-- End of file
------------------------------------------------------------------------

------------------------------------------------------------------------
-- MODULE 3: CLOSED PARTICLE / FIELD / SOURCE EXCHANGE
-- Inlined from RSEDClosedExchange.agda; no local module imports.
------------------------------------------------------------------------
module RSEDClosedExchange where


  module WithRationalRing (Q : RationalRingInterface) where
    open RationalRingInterface Q
    module P = RationalSED Q
    open P
  
    -- Exchange notation aliases the exact rational four-vector addition and
    -- subtraction already defined by RationalSED.
    _⊕_ : Rational4Vector → Rational4Vector → Rational4Vector
    _⊕_ = _+₄_
  
    _⊖_ : Rational4Vector → Rational4Vector → Rational4Vector
    _⊖_ = _-₄_

    ------------------------------------------------------------------------
    -- Exact additive structure inherited from RationalRingInterface.
    ------------------------------------------------------------------------

    refl₄ : (u : Rational4Vector) → u ≡ u
    refl₄ u = refl

    sym₄ : {u v : Rational4Vector} → u ≡ v → v ≡ u
    sym₄ = sym

    trans₄ : {u v w : Rational4Vector} → u ≡ v → v ≡ w → u ≡ w
    trans₄ = trans

    add₄-cong : {u v w z : Rational4Vector} →
                u ≡ v → w ≡ z → (u ⊕ w) ≡ (v ⊕ z)
    add₄-cong refl refl = refl

    zero₄ : Rational4Vector
    zero₄ = r4 0ℚ 0ℚ 0ℚ 0ℚ

    neg₄ : Rational4Vector → Rational4Vector
    neg₄ u =
      r4 (0ℚ -ℚ ct u)
         (0ℚ -ℚ x u)
         (0ℚ -ℚ y u)
         (0ℚ -ℚ z u)

    add₄-assoc : (u v w : Rational4Vector) →
                 ((u ⊕ v) ⊕ w) ≡ (u ⊕ (v ⊕ w))
    add₄-assoc u v w =
      r4-cong
        (+ℚ-assoc (ct u) (ct v) (ct w))
        (+ℚ-assoc (x u) (x v) (x w))
        (+ℚ-assoc (y u) (y v) (y w))
        (+ℚ-assoc (z u) (z v) (z w))

    add₄-comm : (u v : Rational4Vector) → (u ⊕ v) ≡ (v ⊕ u)
    add₄-comm u v =
      r4-cong
        (+ℚ-comm (ct u) (ct v))
        (+ℚ-comm (x u) (x v))
        (+ℚ-comm (y u) (y v))
        (+ℚ-comm (z u) (z v))

    add₄-zeroˡ : (u : Rational4Vector) → (zero₄ ⊕ u) ≡ u
    add₄-zeroˡ u =
      r4-cong
        (+ℚ-zeroˡ (ct u))
        (+ℚ-zeroˡ (x u))
        (+ℚ-zeroˡ (y u))
        (+ℚ-zeroˡ (z u))

    add₄-inverseʳ : (u : Rational4Vector) → (u ⊕ neg₄ u) ≡ zero₄
    add₄-inverseʳ u =
      r4-cong
        (+ℚ-inverseʳ (ct u))
        (+ℚ-inverseʳ (x u))
        (+ℚ-inverseʳ (y u))
        (+ℚ-inverseʳ (z u))

    minus-as-add-neg : (u v : Rational4Vector) →
                       (u ⊖ v) ≡ (u ⊕ neg₄ v)
    minus-as-add-neg u v =
      r4-cong
        (-ℚ-definition (ct u) (ct v))
        (-ℚ-definition (x u) (x v))
        (-ℚ-definition (y u) (y v))
        (-ℚ-definition (z u) (z v))

    -- Middle exchange: u + (v + w) = (u + w) + v.
    add₄-middle : (u v w : Rational4Vector) →
                  (u ⊕ (v ⊕ w)) ≡ ((u ⊕ w) ⊕ v)
    add₄-middle u v w =
      trans₄
        (add₄-cong (refl₄ u) (add₄-comm v w))
        (sym₄ (add₄-assoc u w v))

    -- The transfer and its opposite cancel, without assuming definitional
    -- equality between rational subtraction and addition of an inverse.
    add₄-with-sub-cancel : (d f : Rational4Vector) →
                            (d ⊕ (f ⊖ d)) ≡ f
    add₄-with-sub-cancel d f =
      trans₄
        (add₄-cong (refl₄ d) (minus-as-add-neg f d))
        (trans₄
          (add₄-middle d f (neg₄ d))
          (trans₄
            (add₄-cong (add₄-inverseʳ d) (refl₄ f))
            (add₄-zeroˡ f)))

    pair-exchange-preserves :
      (left right transfer : Rational4Vector) →
      ((left ⊕ transfer) ⊕ (right ⊖ transfer)) ≡ (left ⊕ right)
    pair-exchange-preserves left right transfer =
      trans₄
        (add₄-assoc left transfer (right ⊖ transfer))
        (add₄-cong (refl₄ left)
          (add₄-with-sub-cancel transfer right))

    ------------------------------------------------------------------------
    -- Closed particle / Maxwell-field / source momentum state.
    -- Every elementary update transfers one exact four-vector between two
    -- compartments. No free residual or caller-supplied conservation proof.
    ------------------------------------------------------------------------

    record ClosedMomentumSnapshot : Set where
      constructor closedSnapshot
      field
        particle4Momentum : Rational4Vector
        field4Momentum    : Rational4Vector
        source4Momentum   : Rational4Vector
    open ClosedMomentumSnapshot public

    totalClosedMomentum : ClosedMomentumSnapshot → Rational4Vector
    totalClosedMomentum s =
      particle4Momentum s ⊕ (field4Momentum s ⊕ source4Momentum s)

    data MomentumExchange : Set where
      particleField : Rational4Vector → MomentumExchange
      fieldSource   : Rational4Vector → MomentumExchange

    applyMomentumExchange :
      MomentumExchange → ClosedMomentumSnapshot → ClosedMomentumSnapshot
    applyMomentumExchange (particleField δ) s =
      closedSnapshot
        (particle4Momentum s ⊕ δ)
        (field4Momentum s ⊖ δ)
        (source4Momentum s)
    applyMomentumExchange (fieldSource δ) s =
      closedSnapshot
        (particle4Momentum s)
        (field4Momentum s ⊕ δ)
        (source4Momentum s ⊖ δ)

    particleField-exchange-conserves :
      (δ : Rational4Vector) (s : ClosedMomentumSnapshot) →
      totalClosedMomentum (applyMomentumExchange (particleField δ) s)
        ≡ totalClosedMomentum s
    particleField-exchange-conserves δ s =
      trans₄
        (sym₄
          (add₄-assoc
            (particle4Momentum s ⊕ δ)
            (field4Momentum s ⊖ δ)
            (source4Momentum s)))
        (trans₄
          (add₄-cong
            (pair-exchange-preserves
              (particle4Momentum s) (field4Momentum s) δ)
            (refl₄ (source4Momentum s)))
          (add₄-assoc
            (particle4Momentum s)
            (field4Momentum s)
            (source4Momentum s)))

    fieldSource-exchange-conserves :
      (δ : Rational4Vector) (s : ClosedMomentumSnapshot) →
      totalClosedMomentum (applyMomentumExchange (fieldSource δ) s)
        ≡ totalClosedMomentum s
    fieldSource-exchange-conserves δ s =
      add₄-cong
        (refl₄ (particle4Momentum s))
        (pair-exchange-preserves
          (field4Momentum s) (source4Momentum s) δ)

    exchange-conserves :
      (e : MomentumExchange) (s : ClosedMomentumSnapshot) →
      totalClosedMomentum (applyMomentumExchange e s) ≡ totalClosedMomentum s
    exchange-conserves (particleField δ) s = particleField-exchange-conserves δ s
    exchange-conserves (fieldSource δ) s = fieldSource-exchange-conserves δ s

    runExchanges :
      List MomentumExchange → ClosedMomentumSnapshot → ClosedMomentumSnapshot
    runExchanges [] s = s
    runExchanges (e ∷ es) s = runExchanges es (applyMomentumExchange e s)

    runExchanges-conserves :
      (es : List MomentumExchange) (s : ClosedMomentumSnapshot) →
      totalClosedMomentum (runExchanges es s) ≡ totalClosedMomentum s
    runExchanges-conserves [] s = refl₄ (totalClosedMomentum s)
    runExchanges-conserves (e ∷ es) s =
      trans₄
        (runExchanges-conserves es (applyMomentumExchange e s))
        (exchange-conserves e s)

------------------------------------------------------------------------
-- MODULE 4: Q5-A DEPENDENT RSED MOTIVE
-- Inlined from SovereignRSEDMotive.agda; no local module imports.
------------------------------------------------------------------------
module SovereignRSEDMotive where


  module WithRationalRing (Q : RationalRingInterface) where
    open RationalRingInterface Q
    module P = RationalSED Q
    module Sums = FiniteRationalSums Q
    open Sums public
    open P
    module Closed = RSEDClosedExchange.WithRationalRing Q
    open Closed

    -- A positive cone is explicit semantic data, rather than an unproved
    -- assumption that every rational weight happens to be nonnegative.
    record RationalPositiveCone : Set₂ where
      field
        Nonnegative : Rational → Set
        zeroNonnegative : Nonnegative 0ℚ
        oneNonnegative : Nonnegative 1ℚ
        addNonnegative :
          {a b : Rational} → Nonnegative a → Nonnegative b →
          Nonnegative (a +ℚ b)
        mulNonnegative :
          {a b : Rational} → Nonnegative a → Nonnegative b →
          Nonnegative (a *ℚ b)
    open RationalPositiveCone public

    ------------------------------------------------------------------------
    -- Finite cell labels and list-valued cochains.
    ------------------------------------------------------------------------


    -- A cochain is a length-indexed coefficient vector, so its ambient
    -- cell count is enforced by the type rather than kept as a phantom index.
    Cochain : Nat → Set
    Cochain n = Vec Rational n

    zeroCochain : {n : Nat} → Cochain n
    zeroCochain {n} = replicateVec n 0ℚ

    ------------------------------------------------------------------------
    -- A finite oriented cochain complex C⁰ → C¹ → C² → C³.
    -- Incidence maps satisfy d² = 0 by intensional equality on list encodings.
    ------------------------------------------------------------------------

    record FiniteOrientedCochainComplex : Set₁ where
      field
        n₀ n₁ n₂ n₃ : Nat
        d₀ : Cochain n₀ → Cochain n₁
        d₁ : Cochain n₁ → Cochain n₂
        d₂ : Cochain n₂ → Cochain n₃
        d₁d₀-zero : (a : Cochain n₀) → _≡_ (d₁ (d₀ a)) zeroCochain
        d₂d₁-zero : (a : Cochain n₁) → _≡_ (d₂ (d₁ a)) zeroCochain
        star₂ : Cochain n₂ → Cochain n₂
    open FiniteOrientedCochainComplex public

    faradayFromPotential :
      (K : FiniteOrientedCochainComplex) →
      (A : Cochain (n₁ K)) →
      _≡_ (d₂ K (d₁ K A)) zeroCochain
    faradayFromPotential K A = d₂d₁-zero K A

    ------------------------------------------------------------------------
    -- Finite rational ensemble over complete time trajectories.
    -- A single sample index selects one value at every time/mode, so temporal
    -- correlations are retained rather than resampling independently per time.
    ------------------------------------------------------------------------

    record FiniteRationalTemporalNoise
      (Nonnegative : Rational → Set)
      (samples times modes : Nat) : Set₁ where
      constructor temporalNoise
      field
        probabilityWeight : Nat → Rational
        weightNonnegative :
          (i : Nat) → Nonnegative (probabilityWeight i)
        normalizedWeights :
          sumFinite samples probabilityWeight ≡ 1ℚ
        sampleAmplitude :
          Nat → Nat → Nat → Rational
    open FiniteRationalTemporalNoise public

    noiseMean :
      {Nonnegative : Rational → Set} {samples times modes : Nat} →
      (N : FiniteRationalTemporalNoise Nonnegative samples times modes) →
      Nat → Nat → Rational
    noiseMean {samples = samples} N t m =
      sumFinite samples
        (λ ω → probabilityWeight N ω *ℚ sampleAmplitude N ω t m)

    noiseCovariance :
      {Nonnegative : Rational → Set} {samples times modes : Nat} →
      (N : FiniteRationalTemporalNoise Nonnegative samples times modes) →
      Nat → Nat → Nat → Nat → Rational
    noiseCovariance {samples = samples} N t u m n =
      sumFinite samples
        (λ ω →
          probabilityWeight N ω *ℚ
            ((sampleAmplitude N ω t m -ℚ noiseMean N t m) *ℚ
             (sampleAmplitude N ω u n -ℚ noiseMean N u n)))

    noiseCovariance-symmetric :
      {Nonnegative : Rational → Set} {samples times modes : Nat} →
      (N : FiniteRationalTemporalNoise Nonnegative samples times modes) →
      (t u : Nat) (m n : Nat) →
      noiseCovariance N t u m n ≡ noiseCovariance N u t n m
    noiseCovariance-symmetric {samples = samples} N t u m n =
      sumFinite-cong samples
        (λ ω →
          probabilityWeight N ω *ℚ
            ((sampleAmplitude N ω t m -ℚ noiseMean N t m) *ℚ
             (sampleAmplitude N ω u n -ℚ noiseMean N u n)))
        (λ ω →
          probabilityWeight N ω *ℚ
            ((sampleAmplitude N ω u n -ℚ noiseMean N u n) *ℚ
             (sampleAmplitude N ω t m -ℚ noiseMean N t m)))
        (λ ω →
          cong₂ _*ℚ_
            (refl)
            (*ℚ-comm
              (sampleAmplitude N ω t m -ℚ noiseMean N t m)
              (sampleAmplitude N ω u n -ℚ noiseMean N u n)))

    ------------------------------------------------------------------------
    -- Context and world.  Q5-A: one dependent family over complete worlds.
    ------------------------------------------------------------------------

    record RSEDContext : Set₃ where
      field
        geometry : FiniteOrientedCochainComplex
        positiveCone : RationalPositiveCone
        sampleCount timeCount modeCount : Nat
    open RSEDContext public

    record RSEDWorld (V : RSEDContext) : Set₂ where
      field
        potential : Cochain (n₁ (geometry V))
        sourceCurrent : Cochain (n₃ (geometry V))
        noise : FiniteRationalTemporalNoise
                  (Nonnegative (positiveCone V))
                  (sampleCount V) (timeCount V) (modeCount V)
        initialMomentum : ClosedMomentumSnapshot
        momentumExchanges : List MomentumExchange
    open RSEDWorld public

    fieldStrength :
      {V : RSEDContext} → RSEDWorld V → Cochain (n₂ (geometry V))
    fieldStrength {V} W = d₁ (geometry V) (potential W)

    worldMomentum :
      {V : RSEDContext} → RSEDWorld V → ClosedMomentumSnapshot
    worldMomentum W = runExchanges (momentumExchanges W) (initialMomentum W)

    ------------------------------------------------------------------------
    -- Dependent motive. Q5-A indexes one invariant package over context and
    -- complete semantic world. Only the sourced Maxwell equation is a model
    -- obligation; Faraday, normalized noise, covariance symmetry, and total
    -- momentum conservation are derived from the world structure.
    ------------------------------------------------------------------------

    motiveNoiseNormalization :
      (V : RSEDContext) (W : RSEDWorld V) →
      sumFinite (sampleCount V) (probabilityWeight (noise W)) ≡ 1ℚ
    motiveNoiseNormalization V W = normalizedWeights (noise W)

    motiveNoiseCovarianceSymmetric :
      (V : RSEDContext) (W : RSEDWorld V) →
      (t u : Nat) (m n : Nat) →
      noiseCovariance (noise W) t u m n ≡ noiseCovariance (noise W) u t n m
    motiveNoiseCovarianceSymmetric V W = noiseCovariance-symmetric (noise W)

    motiveFaradayLaw :
      (V : RSEDContext) (W : RSEDWorld V) →
      _≡_
        (d₂ (geometry V) (fieldStrength W))
        zeroCochain
    motiveFaradayLaw V W =
      faradayFromPotential (geometry V) (potential W)

    motiveMomentumConservation :
      (V : RSEDContext) (W : RSEDWorld V) →
      totalClosedMomentum (worldMomentum W)
        ≡ totalClosedMomentum (initialMomentum W)
    motiveMomentumConservation V W =
      runExchanges-conserves (momentumExchanges W) (initialMomentum W)

    record RSEDMotive (V : RSEDContext) (W : RSEDWorld V) : Set₁ where
      field
        maxwellSourceLaw :
          _≡_
            (d₂ (geometry V) (star₂ (geometry V) (fieldStrength W)))
            (sourceCurrent W)
        faradayLaw :
          _≡_
            (d₂ (geometry V) (fieldStrength W))
            zeroCochain
        normalizedNoise :
          sumFinite (sampleCount V) (probabilityWeight (noise W)) ≡ 1ℚ
        covarianceSymmetry :
          (t u : Nat) (m n : Nat) →
          noiseCovariance (noise W) t u m n ≡ noiseCovariance (noise W) u t n m
        totalMomentumConservation :
          totalClosedMomentum (worldMomentum W)
            ≡ totalClosedMomentum (initialMomentum W)
    open RSEDMotive public

    assembleRSEDMotive :
      (V : RSEDContext) (W : RSEDWorld V) →
      _≡_
        (d₂ (geometry V) (star₂ (geometry V) (fieldStrength W)))
        (sourceCurrent W) →
      RSEDMotive V W
    assembleRSEDMotive V W sourced = record
      { maxwellSourceLaw = sourced
      ; faradayLaw = motiveFaradayLaw V W
      ; normalizedNoise = motiveNoiseNormalization V W
      ; covarianceSymmetry = motiveNoiseCovarianceSymmetric V W
      ; totalMomentumConservation = motiveMomentumConservation V W
      }

    -- Any semantic transformation must transport the complete dependent
    -- motive witness along with its world map; transporting only world data is
    -- insufficient because the proof fields depend on that exact world.
    record RSEDWorldMap (V W : RSEDContext) : Set₃ where
      field
        mapWorld : RSEDWorld V → RSEDWorld W
        mapMotive :
          (world : RSEDWorld V) →
          RSEDMotive V world → RSEDMotive W (mapWorld world)
    open RSEDWorldMap public

------------------------------------------------------------------------
-- PHYSICAL FOUNDATIONS: NJ WILDBERGER / FINITE HODGE-MAXWELL / SED
--
-- This module is additive: the foundational packages and their single outer
-- REWRITE registration in SovereignRationalSED remain separate.  It gives
-- the physical layer actual types, equations, and proof
-- obligations rather than treating an arbitrary star map or arbitrary
-- exchange list as a physical realization.
------------------------------------------------------------------------

module RSEDPhysicalFoundations (Q : RationalRingInterface) where

  open RationalRingInterface Q
  module Sums = FiniteRationalSums Q
  open Sums public
  module Relativity = RationalSED Q
  module Exchange = RSEDClosedExchange.WithRationalRing Q

  ----------------------------------------------------------------------
  -- 1. NJ WILDBERGER RATIONAL EUCLIDEAN GEOMETRY
  --
  -- Coordinates, quadrance, dot product, cross product, and spread are
  -- algebraic.  A quotient is represented by an exact numerator,
  -- denominator, and a proof that the denominator is nonzero; no square
  -- roots, angles, or floating-point operations occur.
  ----------------------------------------------------------------------

  record PlaneVector₂ : Set where
    constructor planeVector₂
    field
      vx vy : Rational
  open PlaneVector₂ public

  record Point₂ : Set where
    constructor point₂
    field
      px py : Rational
  open Point₂ public

  difference₂ : Point₂ → Point₂ → PlaneVector₂
  difference₂ p q =
    planeVector₂ (px p -ℚ px q) (py p -ℚ py q)

  dot₂ : PlaneVector₂ → PlaneVector₂ → Rational
  dot₂ u v = (vx u *ℚ vx v) +ℚ (vy u *ℚ vy v)

  cross₂ : PlaneVector₂ → PlaneVector₂ → Rational
  cross₂ u v = (vx u *ℚ vy v) -ℚ (vy u *ℚ vx v)

  quadrance₂ : PlaneVector₂ → Rational
  quadrance₂ u = dot₂ u u

  pointQuadrance₂ : Point₂ → Point₂ → Rational
  pointQuadrance₂ p q = quadrance₂ (difference₂ p q)

  record SpaceVector₃ : Set where
    constructor spaceVector₃
    field
      vx₃ vy₃ vz₃ : Rational
  open SpaceVector₃ public

  record Point₃ : Set where
    constructor point₃
    field
      px₃ py₃ pz₃ : Rational
  open Point₃ public

  difference₃ : Point₃ → Point₃ → SpaceVector₃
  difference₃ p q =
    spaceVector₃ (px₃ p -ℚ px₃ q)
          (py₃ p -ℚ py₃ q)
          (pz₃ p -ℚ pz₃ q)

  dot₃ : SpaceVector₃ → SpaceVector₃ → Rational
  dot₃ u v =
    ((vx₃ u *ℚ vx₃ v) +ℚ (vy₃ u *ℚ vy₃ v)) +ℚ
    (vz₃ u *ℚ vz₃ v)

  quadrance₃ : SpaceVector₃ → Rational
  quadrance₃ u = dot₃ u u

  cross₃ : SpaceVector₃ → SpaceVector₃ → SpaceVector₃
  cross₃ u v =
    spaceVector₃
      ((vy₃ u *ℚ vz₃ v) -ℚ (vz₃ u *ℚ vy₃ v))
      ((vz₃ u *ℚ vx₃ v) -ℚ (vx₃ u *ℚ vz₃ v))
      ((vx₃ u *ℚ vy₃ v) -ℚ (vy₃ u *ℚ vx₃ v))

  pointQuadrance₃ : Point₃ → Point₃ → Rational
  pointQuadrance₃ p q = quadrance₃ (difference₃ p q)

  Nonzero : Rational → Set
  Nonzero r = ¬ (r ≡ 0ℚ)

  record RationalFraction : Set where
    constructor fraction
    field
      numerator denominator : Rational
      denominatorNonzero : Nonzero denominator
  open RationalFraction public

  -- Wildberger's spread, represented exactly as
  -- cross(u,v)^2 / (Q(u) Q(v)).
  rationalSpread₂ : (u v : PlaneVector₂) →
    Nonzero (quadrance₂ u *ℚ quadrance₂ v) → RationalFraction
  rationalSpread₂ u v denominator-proof =
    fraction
      (cross₂ u v *ℚ cross₂ u v)
      (quadrance₂ u *ℚ quadrance₂ v)
      denominator-proof

  -- Three-dimensional spread is the quadrance of the cross product
  -- divided by the product of the two direction quadrances.
  rationalSpread₃ : (u v : SpaceVector₃) →
    Nonzero (quadrance₃ u *ℚ quadrance₃ v) → RationalFraction
  rationalSpread₃ u v denominator-proof =
    fraction
      (quadrance₃ (cross₃ u v))
      (quadrance₃ u *ℚ quadrance₃ v)
      denominator-proof

  record Line₂ : Set where
    constructor line₂
    field
      lineA lineB lineC : Rational
  open Line₂ public

  lineNormalQuadrance₂ : Line₂ → Rational
  lineNormalQuadrance₂ l =
    (lineA l *ℚ lineA l) +ℚ (lineB l *ℚ lineB l)

  lineSpread₂ : (l m : Line₂) →
    Nonzero (lineNormalQuadrance₂ l *ℚ lineNormalQuadrance₂ m) →
    RationalFraction
  lineSpread₂ l m denominator-proof =
    fraction
      (((lineA l *ℚ lineB m) -ℚ (lineA m *ℚ lineB l)) *ℚ
       ((lineA l *ℚ lineB m) -ℚ (lineA m *ℚ lineB l)))
      (lineNormalQuadrance₂ l *ℚ lineNormalQuadrance₂ m)
      denominator-proof

  -- Cramer's rule as exact rational fractions.  This is deliberately a
  -- construction of the coordinates, not a floating-point intersection.
  record RationalLineIntersection₂ (l m : Line₂) : Set where
    constructor lineIntersection₂
    field
      intersectionX intersectionY : RationalFraction
  open RationalLineIntersection₂ public

  lineDeterminant₂ : Line₂ → Line₂ → Rational
  lineDeterminant₂ l m =
    (lineA l *ℚ lineB m) -ℚ (lineA m *ℚ lineB l)

  intersectionFormula₂ : (l m : Line₂) →
    Nonzero (lineDeterminant₂ l m) → RationalLineIntersection₂ l m
  intersectionFormula₂ l m det-nonzero =
    lineIntersection₂
      (fraction
        ((lineB l *ℚ lineC m) -ℚ (lineB m *ℚ lineC l))
        (lineDeterminant₂ l m)
        det-nonzero)
      (fraction
        ((lineC l *ℚ lineA m) -ℚ (lineC m *ℚ lineA l))
        (lineDeterminant₂ l m)
        det-nonzero)

  lineMeetResidual₂ : {l m : Line₂} →
    (line : Line₂) → RationalLineIntersection₂ l m → Rational
  -- Clear both coordinate denominators independently.  For
  -- x = nx/dx and y = ny/dy, the numerator of A*x + B*y + C
  -- over dx*dy is A*nx*dy + B*ny*dx + C*dx*dy.
  -- Keeping dx and dy distinct matters for arbitrary intersections;
  -- the Cramer's-rule constructor happens to choose equal denominators.
  lineMeetResidual₂ line I =
    (((lineA line *ℚ numerator (intersectionX I)) *ℚ
       denominator (intersectionY I)) +ℚ
     ((lineB line *ℚ numerator (intersectionY I)) *ℚ
       denominator (intersectionX I))) +ℚ
    ((lineC line *ℚ denominator (intersectionX I)) *ℚ
      denominator (intersectionY I))

  -- The dot/cross identity and Cramer's-rule incidence are explicit laws
  -- required of each concrete rational plane instance.
  record RationalTrigonometryLawWitness : Set₁ where
    field
      dotCrossQuadrance : (u v : PlaneVector₂) →
        ((dot₂ u v *ℚ dot₂ u v) +ℚ
         (cross₂ u v *ℚ cross₂ u v)) ≡
        (quadrance₂ u *ℚ quadrance₂ v)
      dotCrossQuadrance₃ : (u v : SpaceVector₃) →
        ((dot₃ u v *ℚ dot₃ u v) +ℚ
         quadrance₃ (cross₃ u v)) ≡
        (quadrance₃ u *ℚ quadrance₃ v)
      intersectionOnFirst : (l m : Line₂) →
        (det-nonzero : Nonzero (lineDeterminant₂ l m)) →
        lineMeetResidual₂ l (intersectionFormula₂ l m det-nonzero) ≡ 0ℚ
      intersectionOnSecond : (l m : Line₂) →
        (det-nonzero : Nonzero (lineDeterminant₂ l m)) →
        lineMeetResidual₂ m (intersectionFormula₂ l m det-nonzero) ≡ 0ℚ
  open RationalTrigonometryLawWitness public

  ----------------------------------------------------------------------
  -- 2. FINITE SPATIAL COCHAIN COMPLEX AND METRIC HODGE STRUCTURE
  --
  -- Spatial primal cochains have degrees 0,1,2,3.  Incidence maps are
  -- metric-free and satisfy d²=0.  Positive inner products and their
  -- adjoints are separate metric data.  This distinction is essential:
  -- the spatial Hodge metric is positive definite, while the spacetime
  -- Minkowski metric is Lorentzian.
  ----------------------------------------------------------------------


  -- Cochains are length-indexed vectors. Incidence maps preserve the
  -- cell count in their types; lookup still supplies a default for sparse tails.
  Cochain : Nat → Set
  Cochain n = Vec Rational n

  zeroCochain : {n : Nat} → Cochain n
  zeroCochain {n} = replicateVec n 0ℚ

  addCochain : {n : Nat} → Cochain n → Cochain n → Cochain n
  addCochain {n} xs ys =
    tabulateVec n (λ i →
      lookupVecOr 0ℚ i xs +ℚ lookupVecOr 0ℚ i ys)

  negCochain : {n : Nat} → Cochain n → Cochain n
  negCochain {n} xs =
    tabulateVec n (λ i → 0ℚ -ℚ lookupVecOr 0ℚ i xs)

  subCochain : {n : Nat} → Cochain n → Cochain n → Cochain n
  subCochain f g = addCochain f (negCochain g)

  scaleCochain : {n : Nat} → Rational → Cochain n → Cochain n
  scaleCochain {n} r xs =
    tabulateVec n (λ i → r *ℚ lookupVecOr 0ℚ i xs)

  ----------------------------------------------------------------------
  -- A finite embedded rational 3D cell complex.  Incidence coefficients
  -- are typed signs (−1,0,+1), not arbitrary floating weights.  Edge
  -- lengths/quadrances come from the embedded rational vertex positions.
  ----------------------------------------------------------------------

  record OrientedEdge (vertices : Nat) : Set where
    constructor orientedEdge
    field
      edgeSource edgeTarget : Nat
      edgeSourceBound : (edgeSource < vertices) ≡ true
      edgeTargetBound : (edgeTarget < vertices) ≡ true
  open OrientedEdge public

  data IncidenceSign : Set where
    minusSign zeroSign plusSign : IncidenceSign

  incidenceValue : IncidenceSign → Rational
  incidenceValue minusSign = 0ℚ -ℚ 1ℚ
  incidenceValue zeroSign = 0ℚ
  incidenceValue plusSign = 1ℚ

  record FiniteRationalMesh3D : Set₂ where
    field
      vertexCount edgeCount faceCount cellCount : Nat
      vertexPosition : Nat → Point₃
      orientedEdgeAt : Nat → OrientedEdge vertexCount
      faceBoundary : Nat → Nat → IncidenceSign
      cellBoundary : Nat → Nat → IncidenceSign
  open FiniteRationalMesh3D public

  meshEdgeQuadrance :
    (M : FiniteRationalMesh3D) → Nat → Rational
  meshEdgeQuadrance M e =
    pointQuadrance₃
      (vertexPosition M (edgeSource (orientedEdgeAt M e)))
      (vertexPosition M (edgeTarget (orientedEdgeAt M e)))

  meshGradient :
    (M : FiniteRationalMesh3D) →
    Cochain (vertexCount M) → Cochain (edgeCount M)
  meshGradient M potential =
    tabulateVec (edgeCount M) (λ e →
      lookupVecOr 0ℚ (edgeTarget (orientedEdgeAt M e)) potential -ℚ
      lookupVecOr 0ℚ (edgeSource (orientedEdgeAt M e)) potential)

  meshCurl :
    (M : FiniteRationalMesh3D) →
    Cochain (edgeCount M) → Cochain (faceCount M)
  meshCurl M edgeField =
    tabulateVec (faceCount M) (λ f →
      sumFinite (edgeCount M)
        (λ e → incidenceValue (faceBoundary M f e) *ℚ
          lookupVecOr 0ℚ e edgeField))

  meshDivergence :
    (M : FiniteRationalMesh3D) →
    Cochain (faceCount M) → Cochain (cellCount M)
  meshDivergence M faceField =
    tabulateVec (cellCount M) (λ c →
      sumFinite (faceCount M)
        (λ f → incidenceValue (cellBoundary M c f) *ℚ
          lookupVecOr 0ℚ f faceField))

  record MeshBoundaryProof (M : FiniteRationalMesh3D) : Set₁ where
    field
      faceBoundaryOfBoundary :
        (potential : Cochain (vertexCount M)) →
        _≡_ (meshCurl M (meshGradient M potential)) zeroCochain
      cellBoundaryOfBoundary :
        (edgeField : Cochain (edgeCount M)) →
        _≡_ (meshDivergence M (meshCurl M edgeField)) zeroCochain
  open MeshBoundaryProof public

  record FiniteSpatialCochainComplex : Set₁ where
    field
      n₀ n₁ n₂ n₃ : Nat
      d₀ : Cochain n₀ → Cochain n₁
      d₁ : Cochain n₁ → Cochain n₂
      d₂ : Cochain n₂ → Cochain n₃
      d₁d₀-zero : (a : Cochain n₀) →
        _≡_ (d₁ (d₀ a)) zeroCochain
      d₂d₁-zero : (a : Cochain n₁) →
        _≡_ (d₂ (d₁ a)) zeroCochain
  open FiniteSpatialCochainComplex public

  meshCochainComplex :
    (M : FiniteRationalMesh3D) → MeshBoundaryProof M →
    FiniteSpatialCochainComplex
  meshCochainComplex M boundary = record
    { n₀ = vertexCount M
    ; n₁ = edgeCount M
    ; n₂ = faceCount M
    ; n₃ = cellCount M
    ; d₀ = meshGradient M
    ; d₁ = meshCurl M
    ; d₂ = meshDivergence M
    ; d₁d₀-zero = faceBoundaryOfBoundary boundary
    ; d₂d₁-zero = cellBoundaryOfBoundary boundary
    }

  record RationalPositivity : Set₂ where
    field
      Nonnegative : Rational → Set
      Positive : Rational → Set
      zeroNonnegative : Nonnegative 0ℚ
      onePositive : Positive 1ℚ
      positiveNonnegative : {x : Rational} →
        Positive x → Nonnegative x
      positiveNonzero : {x : Rational} →
        Positive x → Nonzero x
      squareNonnegative : (x : Rational) → Nonnegative (x *ℚ x)
      addNonnegative : {x y : Rational} →
        Nonnegative x → Nonnegative y → Nonnegative (x +ℚ y)
      multiplyNonnegative : {x y : Rational} →
        Nonnegative x → Nonnegative y → Nonnegative (x *ℚ y)
      multiplyPositive : {x y : Rational} →
        Positive x → Positive y → Positive (x *ℚ y)
  open RationalPositivity public

  -- Future-directed timelike vectors use the chosen exact positive cone.
  -- The algebraic Cayley certificate in the core preserves quadrance; this
  -- stricter wrapper also rejects the denominator-negative, time-reversing
  -- branch (for example parameter=3 in ordinary rational arithmetic).
  FutureTimelike : (P : RationalPositivity) →
    Relativity.Rational4Vector → Set
  FutureTimelike P u =
    Positive P (Relativity.ct u) ×
    Positive P (Relativity.minkowskiQuadrance u)

  record OrthoChronousCayleyPlaneBoost
    (P : RationalPositivity) : Set₁ where
    field
      algebraicBoost : Relativity.CertifiedCayleyPlaneBoost
      positiveBoostDenominator :
        Positive P (Relativity.CertifiedCayleyPlaneBoost.denominator algebraicBoost)
      preservesFutureCone : (u : Relativity.Rational4Vector) →
        FutureTimelike P u →
        FutureTimelike P (Relativity.applyCayleyPlaneBoost algebraicBoost u)
  open OrthoChronousCayleyPlaneBoost public

  applyOrthoChronousCayleyPlaneBoost :
    {P : RationalPositivity} →
    OrthoChronousCayleyPlaneBoost P →
    Relativity.Rational4Vector → Relativity.Rational4Vector
  applyOrthoChronousCayleyPlaneBoost B =
    Relativity.applyCayleyPlaneBoost (algebraicBoost B)

  record RationalInnerProduct (P : RationalPositivity) (n : Nat) : Set₁ where
    field
      inner : Cochain n → Cochain n → Rational
      inner-cong : {x y u v : Cochain n} →
        _≡_ x y → _≡_ u v →
        inner x u ≡ inner y v
      inner-symmetric : (x y : Cochain n) →
        inner x y ≡ inner y x
      inner-zero-left : (x : Cochain n) →
        inner zeroCochain x ≡ 0ℚ
      inner-add-left : (x y z : Cochain n) →
        inner (addCochain x y) z ≡
        (inner x z +ℚ inner y z)
      inner-scale-left : (a : Rational) (x y : Cochain n) →
        inner (scaleCochain a x) y ≡ (a *ℚ inner x y)
      inner-norm-nonnegative : (x : Cochain n) →
        Nonnegative P (inner x x)
      inner-norm-positive : (x : Cochain n) →
        ¬ _≡_ x zeroCochain → Positive P (inner x x)
      positive-definite : (x : Cochain n) →
        inner x x ≡ 0ℚ → _≡_ x zeroCochain
  open RationalInnerProduct public

  -- Dual cochains are distinct Agda types.  Dual k-cells correspond to
  -- primal (3-k)-cells, so their counts reverse: dual C⁰ has one value per
  -- primal 3-cell, dual C¹ per primal 2-cell, etc.
  record DualCochain₀ (M : FiniteRationalMesh3D) : Set where
    constructor dualCochain₀
    field dual₀Values : Cochain (cellCount M)
  open DualCochain₀ public

  record DualCochain₁ (M : FiniteRationalMesh3D) : Set where
    constructor dualCochain₁
    field dual₁Values : Cochain (faceCount M)
  open DualCochain₁ public

  record DualCochain₂ (M : FiniteRationalMesh3D) : Set where
    constructor dualCochain₂
    field dual₂Values : Cochain (edgeCount M)
  open DualCochain₂ public

  record DualCochain₃ (M : FiniteRationalMesh3D) : Set where
    constructor dualCochain₃
    field dual₃Values : Cochain (vertexCount M)
  open DualCochain₃ public

  record DualSpatialCochainComplex (M : FiniteRationalMesh3D) : Set₁ where
    field
      dualD₀ : DualCochain₀ M → DualCochain₁ M
      dualD₁ : DualCochain₁ M → DualCochain₂ M
      dualD₂ : DualCochain₂ M → DualCochain₃ M
      dualD₁D₀-zero : (a : DualCochain₀ M) →
        _≡_ (dual₂Values (dualD₁ (dualD₀ a))) zeroCochain
      dualD₂D₁-zero : (a : DualCochain₁ M) →
        _≡_ (dual₃Values (dualD₂ (dualD₁ a))) zeroCochain
  open DualSpatialCochainComplex public

  record MetricHodgeComplex (P : RationalPositivity) : Set₂ where
    field
      mesh : FiniteRationalMesh3D
      meshBoundaryProof : MeshBoundaryProof mesh
      dualComplex : DualSpatialCochainComplex mesh
      metric₀ : RationalInnerProduct P (vertexCount mesh)
      metric₁ : RationalInnerProduct P (edgeCount mesh)
      metric₂ : RationalInnerProduct P (faceCount mesh)
      metric₃ : RationalInnerProduct P (cellCount mesh)
      dualMetric₀ : RationalInnerProduct P (cellCount mesh)
      dualMetric₁ : RationalInnerProduct P (faceCount mesh)
      dualMetric₂ : RationalInnerProduct P (edgeCount mesh)
      dualMetric₃ : RationalInnerProduct P (vertexCount mesh)
      -- Hodge stars map primal k-cochains to dual (3-k)-cochains.
      -- Inverses have the genuinely dual types; primal C¹ and C² need not
      -- have equal dimensions.
      star₀ : Cochain (vertexCount mesh) → DualCochain₃ mesh
      star₁ : Cochain (edgeCount mesh) → DualCochain₂ mesh
      star₂ : Cochain (faceCount mesh) → DualCochain₁ mesh
      star₃ : Cochain (cellCount mesh) → DualCochain₀ mesh
      invStar₀ : DualCochain₃ mesh → Cochain (vertexCount mesh)
      invStar₁ : DualCochain₂ mesh → Cochain (edgeCount mesh)
      invStar₂ : DualCochain₁ mesh → Cochain (faceCount mesh)
      invStar₃ : DualCochain₀ mesh → Cochain (cellCount mesh)
      invStar₀-star₀-id : (a : Cochain (vertexCount mesh)) →
        _≡_ (invStar₀ (star₀ a)) a
      star₀-invStar₀-id : (a : DualCochain₃ mesh) →
        _≡_ (dual₃Values (star₀ (invStar₀ a))) (dual₃Values a)
      invStar₁-star₁-id : (a : Cochain (edgeCount mesh)) →
        _≡_ (invStar₁ (star₁ a)) a
      star₁-invStar₁-id : (a : DualCochain₂ mesh) →
        _≡_ (dual₂Values (star₁ (invStar₁ a))) (dual₂Values a)
      invStar₂-star₂-id : (a : Cochain (faceCount mesh)) →
        _≡_ (invStar₂ (star₂ a)) a
      star₂-invStar₂-id : (a : DualCochain₁ mesh) →
        _≡_ (dual₁Values (star₂ (invStar₂ a))) (dual₁Values a)
      invStar₃-star₃-id : (a : Cochain (cellCount mesh)) →
        _≡_ (invStar₃ (star₃ a)) a
      star₃-invStar₃-id : (a : DualCochain₀ mesh) →
        _≡_ (dual₀Values (star₃ (invStar₃ a))) (dual₀Values a)
      star₀-isometry : (a b : Cochain (vertexCount mesh)) →
        inner dualMetric₃ (dual₃Values (star₀ a)) (dual₃Values (star₀ b))
          ≡ inner metric₀ a b
      star₁-isometry : (a b : Cochain (edgeCount mesh)) →
        inner dualMetric₂ (dual₂Values (star₁ a)) (dual₂Values (star₁ b))
          ≡ inner metric₁ a b
      star₂-isometry : (a b : Cochain (faceCount mesh)) →
        inner dualMetric₁ (dual₁Values (star₂ a)) (dual₁Values (star₂ b))
          ≡ inner metric₂ a b
      star₃-isometry : (a b : Cochain (cellCount mesh)) →
        inner dualMetric₀ (dual₀Values (star₃ a)) (dual₀Values (star₃ b))
          ≡ inner metric₃ a b
      δ₁ : Cochain (edgeCount mesh) → Cochain (vertexCount mesh)
      δ₂ : Cochain (faceCount mesh) → Cochain (edgeCount mesh)
      δ₃ : Cochain (cellCount mesh) → Cochain (faceCount mesh)
      -- In dimension three: δ₁ = -*⁻¹₀ d*₂ *, δ₂ = *⁻¹₁ d*₁ *,
      -- δ₃ = -*⁻¹₂ d*₀ *.  Dual coboundaries act on dual cells.
      δ₁-hodge-star : (a : Cochain (edgeCount mesh)) →
        _≡_ (δ₁ a)
          (negCochain (invStar₀ (dualD₂ dualComplex (star₁ a))))
      δ₂-hodge-star : (a : Cochain (faceCount mesh)) →
        _≡_ (δ₂ a)
          (invStar₁ (dualD₁ dualComplex (star₂ a)))
      δ₃-hodge-star : (a : Cochain (cellCount mesh)) →
        _≡_ (δ₃ a)
          (negCochain (invStar₂ (dualD₀ dualComplex (star₃ a))))
      adjoint-d₀ : (a : Cochain (vertexCount mesh)) →
        (b : Cochain (edgeCount mesh)) →
        inner metric₁ (meshGradient mesh a) b ≡
        inner metric₀ a (δ₁ b)
      adjoint-d₁ : (a : Cochain (edgeCount mesh)) →
        (b : Cochain (faceCount mesh)) →
        inner metric₂ (meshCurl mesh a) b ≡
        inner metric₁ a (δ₂ b)
      adjoint-d₂ : (a : Cochain (faceCount mesh)) →
        (b : Cochain (cellCount mesh)) →
        inner metric₃ (meshDivergence mesh a) b ≡
        inner metric₂ a (δ₃ b)
      δ₁δ₂-zero : (b : Cochain (faceCount mesh)) →
        _≡_ (δ₁ (δ₂ b)) zeroCochain
      δ₂δ₃-zero : (c : Cochain (cellCount mesh)) →
        _≡_ (δ₂ (δ₃ c)) zeroCochain
      edgeQuadrancePositive : (e : Nat) →
        Positive P (meshEdgeQuadrance mesh e)
  open MetricHodgeComplex public

  complex : {P : RationalPositivity} →
    MetricHodgeComplex P → FiniteSpatialCochainComplex
  complex H = meshCochainComplex (mesh H) (meshBoundaryProof H)


  hodgeLaplacian₁ : {P : RationalPositivity} → (H : MetricHodgeComplex P) →
    Cochain (n₁ (complex H)) → Cochain (n₁ (complex H))
  hodgeLaplacian₁ H x =
    addCochain
      (d₀ (complex H) (δ₁ H x))
      (δ₂ H (d₁ (complex H) x))

  hodgeLaplacian₂ : {P : RationalPositivity} → (H : MetricHodgeComplex P) →
    Cochain (n₂ (complex H)) → Cochain (n₂ (complex H))
  hodgeLaplacian₂ H x =
    addCochain
      (d₁ (complex H) (δ₂ H x))
      (δ₃ H (d₂ (complex H) x))

  Harmonic₂ : {P : RationalPositivity} → (H : MetricHodgeComplex P) → Cochain (n₂ (complex H)) → Set
  Harmonic₂ H x =
    (_≡_ (d₂ (complex H) x) zeroCochain) ×
    (_≡_ (δ₂ H x) zeroCochain)

  -- Degree-one Hodge split: exact gradients, co-exact curls, and harmonic
  -- 1-cochains. Each component carries its actual preimage.
  record HodgeDecomposition₁
    {P : RationalPositivity}
    (H : MetricHodgeComplex P)
    (field₁ : Cochain (n₁ (complex H))) : Set₁ where
    field
      exactPotential₁ : Cochain (n₀ (complex H))
      coexactPotential₁ : Cochain (n₂ (complex H))
      harmonicPart₁ : Cochain (n₁ (complex H))
      reconstructs₁ : _≡_ field₁
        (addCochain
          (addCochain
            (d₀ (complex H) exactPotential₁)
            (δ₂ H coexactPotential₁))
          harmonicPart₁)
      harmonicClosed₁ : _≡_
        (d₁ (complex H) harmonicPart₁) zeroCochain
      harmonicCoclosed₁ : _≡_
        (δ₁ H harmonicPart₁) zeroCochain
      exactCoexactOrthogonal₁ :
        inner (metric₁ H)
          (d₀ (complex H) exactPotential₁)
          (δ₂ H coexactPotential₁) ≡ 0ℚ
      exactHarmonicOrthogonal₁ :
        inner (metric₁ H)
          (d₀ (complex H) exactPotential₁) harmonicPart₁ ≡ 0ℚ
      coexactHarmonicOrthogonal₁ :
        inner (metric₁ H)
          (δ₂ H coexactPotential₁) harmonicPart₁ ≡ 0ℚ
  open HodgeDecomposition₁ public

  -- Degree-two Hodge split: exact, co-exact, and harmonic 2-cochains.
  -- Each component carries its actual preimage and proof obligations.
  record HodgeDecomposition₂
    {P : RationalPositivity}
    (H : MetricHodgeComplex P)
    (field₂ : Cochain (n₂ (complex H))) : Set₁ where
    field
      exactPotential : Cochain (n₁ (complex H))
      coexactPotential : Cochain (n₃ (complex H))
      harmonicPart : Cochain (n₂ (complex H))
      reconstructs : _≡_ field₂
        (addCochain
          (addCochain
            (d₁ (complex H) exactPotential)
            (δ₃ H coexactPotential))
          harmonicPart)
      harmonicClosed : _≡_
        (d₂ (complex H) harmonicPart) zeroCochain
      harmonicCoclosed : _≡_
        (δ₂ H harmonicPart) zeroCochain
      exactCoexactOrthogonal :
        inner (metric₂ H)
          (d₁ (complex H) exactPotential)
          (δ₃ H coexactPotential) ≡ 0ℚ
      exactHarmonicOrthogonal :
        inner (metric₂ H)
          (d₁ (complex H) exactPotential) harmonicPart ≡ 0ℚ
      coexactHarmonicOrthogonal :
        inner (metric₂ H)
          (δ₃ H coexactPotential) harmonicPart ≡ 0ℚ
  open HodgeDecomposition₂ public

  ----------------------------------------------------------------------
  -- 3. HODGE-MAXWELL: SPATIAL FINITE-DIMENSIONAL EQUATIONS
  --
  -- E is a primal 1-cochain and B is a primal 2-cochain.  The equations
  -- use the metric adjoints δ, not an arbitrary untyped star₂.  A midpoint
  -- step is a proof-carrying exact rational update.  Its work identity is
  -- part of the step contract and can be checked from a concrete solver.
  ----------------------------------------------------------------------

  record MaxwellState {P : RationalPositivity} (H : MetricHodgeComplex P) : Set₁ where
    field
      electricField : Cochain (n₁ (complex H))
      magneticField : Cochain (n₂ (complex H))
      chargeDensity : Cochain (n₀ (complex H))
      gaussElectric : _≡_ (δ₁ H electricField) chargeDensity
      gaussMagnetic : _≡_
        (d₂ (complex H) magneticField) zeroCochain
  open MaxwellState public

  twice : Rational
  twice = 1ℚ +ℚ 1ℚ

  record MaxwellMidpointStep
    {P : RationalPositivity}
    (H : MetricHodgeComplex P)
    (dt : Rational)
    (current : Cochain (n₁ (complex H)))
    (before after : MaxwellState H) : Set₁ where
    field
      faradayMidpoint : _≡_
        (scaleCochain twice
          (subCochain (magneticField after) (magneticField before)))
        (scaleCochain (0ℚ -ℚ dt)
          (d₁ (complex H)
            (addCochain (electricField before) (electricField after))))
      ampereMidpoint : _≡_
        (scaleCochain twice
          (subCochain (electricField after) (electricField before)))
        (scaleCochain dt
          (subCochain
            (δ₂ H (addCochain (magneticField before) (magneticField after)))
            (scaleCochain twice current)))
      chargeContinuity : _≡_
        (scaleCochain twice
          (subCochain (chargeDensity after) (chargeDensity before)))
        (scaleCochain (0ℚ -ℚ dt)
          (δ₁ H (scaleCochain twice current)))
      -- Twice the field energy is <E,E> + <B,B>.  Thus this exact identity
      -- is Δ(2U) = -dt <E_before+E_after,J>, i.e. midpoint current work.
      exactDiscreteWorkBalance :
        ((inner (metric₁ H) (electricField after) (electricField after) +ℚ
          inner (metric₂ H) (magneticField after) (magneticField after)) -ℚ
         (inner (metric₁ H) (electricField before) (electricField before) +ℚ
          inner (metric₂ H) (magneticField before) (magneticField before)))
        ≡
        ((0ℚ -ℚ dt) *ℚ
          inner (metric₁ H)
            (addCochain (electricField before) (electricField after))
            current)
  open MaxwellMidpointStep public

  ----------------------------------------------------------------------
  -- 4. FINITE RATIONAL STOCHASTIC ELECTRODYNAMICS: AXIOM INPUT
  --
  -- Standard SED core assumptions (Boyer):
  --
  --   SED-1. Maxwell's equations hold with point-charge sources.
  --   SED-2. Charged point particles obey relativistic Lorentz-force
  --          dynamics.
  --   SED-3. The source-free Maxwell sector contains classical random
  --          zero-point radiation with a Lorentz-invariant spectrum and
  --          energy hbar*omega/2 per normal mode.
  --
  -- Constructive scope of this file:
  --   * Rational coefficients and finite sample weights are explicit.
  --   * Time and mode labels are Nat-indexed; finite sums use an explicit
  --     Nat cutoff.
  --   * Means, covariance, and the omega^3 finite-band law are supplied
  --     as model data below, not derived from Maxwell's equations.
  --   * The field-quadratic covariance C_E + C_B = hbar*omega represents
  --     twice the mode energy, since U=(E^2+B^2)/2 in this normalization.
  --   * densityNormalization absorbs the rational finite-grid calibration;
  --     exact pi, c, continuum integrals, and continuum limits are absent.
  --
  -- This finite vacuum-side contract does not yet encode point-particle
  -- Lorentz-force dynamics, a sourced particle/field coupling, or a full
  -- continuous Lorentz-group action. In particular, an omega^3 law on a
  -- rational mode grid is not itself a proof of Lorentz invariance.
  -- No Gaussianity assumption is introduced.
  --
  -- Keep assumptions in FiniteSEDVacuumAxioms. Derived finite identities
  -- and theorems belong in the later sections, outside this record.
  ----------------------------------------------------------------------

  record FiniteTimeAction (times : Nat) : Set₁ where
    field
      -- An explicit origin makes the finite time index nonempty by construction.
      timeOrigin : Nat
      timeStep : Nat
      translateTime : Nat → Nat → Nat
      nextTime : Nat → Nat
      translate-origin : (t : Nat) →
        translateTime t timeOrigin ≡ t
      translate-compose : (t s r : Nat) →
        translateTime (translateTime t s) r ≡
        translateTime t (translateTime s r)
      next-is-translation : (t : Nat) →
        nextTime t ≡ translateTime t timeStep
  open FiniteTimeAction public

  record FiniteSEDEnsemble
    (P : RationalPositivity)
    (samples times modes : Nat) : Set₁ where
    field
      probabilityWeight : Nat → Rational
      weightNonnegative : (w : Nat) →
        Nonnegative P (probabilityWeight w)
      normalizedWeights :
        sumFinite samples probabilityWeight ≡ 1ℚ
      electricAmplitude : Nat → Nat → Nat → Rational
      magneticAmplitude : Nat → Nat → Nat → Rational
  open FiniteSEDEnsemble public

  componentAmplitude :
    {P : RationalPositivity} {samples times modes : Nat} →
    FiniteSEDEnsemble P samples times modes →
    Nat → Nat → Nat → Bool → Rational
  componentAmplitude N w t m true = electricAmplitude N w t m
  componentAmplitude N w t m false = magneticAmplitude N w t m

  stochasticMean :
    {P : RationalPositivity} {samples times modes : Nat} →
    (N : FiniteSEDEnsemble P samples times modes) →
    Nat → Nat → Bool → Rational
  stochasticMean {samples = samples} N t m electric? =
    sumFinite samples
      (λ w → probabilityWeight N w *ℚ
        componentAmplitude N w t m electric?)

  stochasticCovariance :
    {P : RationalPositivity} {samples times modes : Nat} →
    (N : FiniteSEDEnsemble P samples times modes) →
    Nat → Nat → Nat → Nat → Bool → Bool → Rational
  stochasticCovariance {samples = samples} N t u m n electric? magnetic? =
    sumFinite samples
      (λ w → probabilityWeight N w *ℚ
        ((componentAmplitude N w t m electric? -ℚ
          stochasticMean N t m electric?) *ℚ
         (componentAmplitude N w u n magnetic? -ℚ
          stochasticMean N u n magnetic?)))

  stochasticCovariance-symmetric :
    {P : RationalPositivity} {samples times modes : Nat} →
    (N : FiniteSEDEnsemble P samples times modes) →
    (t u : Nat) (m n : Nat) (e b : Bool) →
    stochasticCovariance N t u m n e b ≡
    stochasticCovariance N u t n m b e
  stochasticCovariance-symmetric {samples = samples} N t u m n e b =
    sumFinite-cong samples
      (λ w → probabilityWeight N w *ℚ
        ((componentAmplitude N w t m e -ℚ stochasticMean N t m e) *ℚ
         (componentAmplitude N w u n b -ℚ stochasticMean N u n b)))
      (λ w → probabilityWeight N w *ℚ
        ((componentAmplitude N w u n b -ℚ stochasticMean N u n b) *ℚ
         (componentAmplitude N w t m e -ℚ stochasticMean N t m e)))
      (λ w →
        cong₂ _*ℚ_
          (refl)
          (*ℚ-comm
            (componentAmplitude N w t m e -ℚ stochasticMean N t m e)
            (componentAmplitude N w u n b -ℚ stochasticMean N u n b)))

  sumNonnegative :
    (P : RationalPositivity) →
    (n : Nat) → (f : Nat → Rational) →
    ((i : Nat) → Nonnegative P (f i)) →
    Nonnegative P (sumFinite n f)
  sumNonnegative P zero f nonnegative = zeroNonnegative P
  sumNonnegative P (suc n) f nonnegative =
    addNonnegative P
      (nonnegative zero)
      (sumNonnegative P n (λ i → f (suc i))
        (λ i → nonnegative (suc i)))

  stochasticVarianceNonnegative :
    {P : RationalPositivity} {samples times modes : Nat} →
    (N : FiniteSEDEnsemble P samples times modes) →
    (t : Nat) (m : Nat) (electric? : Bool) →
    Nonnegative P (stochasticCovariance N t t m m electric? electric?)
  stochasticVarianceNonnegative {P} {samples} N t m electric? =
    sumNonnegative P samples
      (λ w → probabilityWeight N w *ℚ
        ((componentAmplitude N w t m electric? -ℚ
          stochasticMean N t m electric?) *ℚ
         (componentAmplitude N w t m electric? -ℚ
          stochasticMean N t m electric?)))
      (λ w →
        multiplyNonnegative P
          (weightNonnegative N w)
          (squareNonnegative P
            (componentAmplitude N w t m electric? -ℚ
             stochasticMean N t m electric?)))

  -- A Nat-indexed discrete time-translation action makes temporal
  -- stationarity an explicit assumption on the covariance kernel. It says
  -- nothing about spatial homogeneity or Lorentz invariance.
  -- Axioms are supplied as fields; they are not declared as Agda
  -- postulates. A concrete finite model must provide witnesses for each
  -- statistical and spectral assumption.
  record FiniteSEDVacuumAxioms
    (P : RationalPositivity)
    (samples times modes : Nat) : Set₂ where
    field
      ensemble : FiniteSEDEnsemble P samples times modes
      timeAction : FiniteTimeAction times
      meanZeroElectric : (t : Nat) (m : Nat) →
        stochasticMean ensemble t m true ≡ 0ℚ
      meanZeroMagnetic : (t : Nat) (m : Nat) →
        stochasticMean ensemble t m false ≡ 0ℚ
      timeTranslationStationary :
        (t u s : Nat) (m n : Nat) (e b : Bool) →
        stochasticCovariance ensemble
          (translateTime timeAction t s)
          (translateTime timeAction u s) m n e b ≡
        stochasticCovariance ensemble t u m n e b
      modeFrequency : Nat → Rational
      frequencyPositive : (m : Nat) →
        Positive P (modeFrequency m)
      hbarScale : Rational
      hbarScalePositive : Positive P hbarScale
      -- With U_mode = (E_mode^2 + B_mode^2)/2, the sum of the
      -- electric and magnetic variances equals hbar*omega. Thus the
      -- expected mode energy is hbar*omega/2; no extra factor is missing.
      modeEnergyCovariance : (t : Nat) (m : Nat) →
        (stochasticCovariance ensemble t t m m true true +ℚ
         stochasticCovariance ensemble t t m m false false)
        ≡ (hbarScale *ℚ modeFrequency m)
      densityNormalization : Rational
      densityNormalizationPositive : Positive P densityNormalization
      densityScale : Rational
      densityScalePositive : Positive P densityScale
      densityScaleLaw :
        densityScale ≡ (hbarScale *ℚ densityNormalization)
      spectralDensity : Nat → Rational
      spectralDensityPositive : (m : Nat) →
        Positive P (spectralDensity m)
      -- Three-dimensional zero-point energy density target, on a finite
      -- rational frequency grid.  The exact irrational constants and
      -- continuum limit are deliberately not smuggled into Rational.
      omegaCubedLaw : (m : Nat) →
        spectralDensity m ≡
        (densityScale *ℚ
          (modeFrequency m *ℚ
           (modeFrequency m *ℚ modeFrequency m)))
  open FiniteSEDVacuumAxioms public

  ----------------------------------------------------------------------
  -- CONATURAL INFINITE-HORIZON STATIONARY COVARIANCE ORBIT
  --
  -- The finite solver remains indexed by finite time labels.  The finite
  -- time-translation action induces a productive, potentially infinite
  -- orbit of covariance observations.  This is an infinite translation
  -- history over the finite model, not a claim of a continuum-time limit.
  ----------------------------------------------------------------------

  advanceCovarianceShift : {times : Nat} →
    (A : FiniteTimeAction times) → Nat → Nat
  advanceCovarianceShift A shift = translateTime A shift (timeStep A)

  covarianceAtShift :
    {P : RationalPositivity} {samples times modes : Nat} →
    (V : FiniteSEDVacuumAxioms P samples times modes) →
    Nat → Nat → Nat → Nat → Bool → Bool →
    Nat → Rational
  covarianceAtShift V t u m n e b shift =
    stochasticCovariance (ensemble V)
      (translateTime (timeAction V) t shift)
      (translateTime (timeAction V) u shift) m n e b

  covarianceAtShift-stationary :
    {P : RationalPositivity} {samples times modes : Nat} →
    (V : FiniteSEDVacuumAxioms P samples times modes) →
    (t u : Nat) (m n : Nat) (e b : Bool) →
    (shift : Nat) →
    covarianceAtShift V t u m n e b shift ≡
    stochasticCovariance (ensemble V) t u m n e b
  covarianceAtShift-stationary V t u m n e b shift =
    timeTranslationStationary V t u shift m n e b

  covarianceOrbitFromShift :
    {P : RationalPositivity} {samples times modes : Nat} →
    (V : FiniteSEDVacuumAxioms P samples times modes) →
    (t u : Nat) (m n : Nat) (e b : Bool) →
    Nat → ConatStream Rational
  covarianceOrbitFromShift V t u m n e b initialShift =
    mapConatStream
      (covarianceAtShift V t u m n e b)
      (iterateConat (advanceCovarianceShift (timeAction V))
        infinity initialShift)

  covarianceOrbitFromShift-head :
    {P : RationalPositivity} {samples times modes : Nat} →
    (V : FiniteSEDVacuumAxioms P samples times modes) →
    (t u : Nat) (m n : Nat) (e b : Bool) →
    (shift : Nat) →
    observeStream (covarianceOrbitFromShift V t u m n e b shift) ≡
    just (pair (covarianceAtShift V t u m n e b shift)
      (covarianceOrbitFromShift V t u m n e b
        (advanceCovarianceShift (timeAction V) shift)))
  covarianceOrbitFromShift-head V t u m n e b shift = refl

  covarianceOrbitPrefix :
    {P : RationalPositivity} {samples times modes : Nat} →
    (V : FiniteSEDVacuumAxioms P samples times modes) →
    Nat → (t u : Nat) → (m n : Nat) → Bool → Bool →
    Nat → Rational
  covarianceOrbitPrefix V depth t u m n e b shift =
    foldConatPrefix _+ℚ_ 0ℚ depth
      (covarianceOrbitFromShift V t u m n e b shift)

  repeatRationalSum : Nat → Rational → Rational
  repeatRationalSum zero value = 0ℚ
  repeatRationalSum (suc depth) value =
    value +ℚ repeatRationalSum depth value

  -- Every finite prefix of the infinite covariance orbit sums the same
  -- stationary covariance value once per observation.  This is a theorem,
  -- not an assumed convergence result or an infinite arithmetic oracle.
  covarianceOrbitPrefix-stationary :
    {P : RationalPositivity} {samples times modes : Nat} →
    (V : FiniteSEDVacuumAxioms P samples times modes) →
    (depth : Nat) → (t u : Nat) →
    (m n : Nat) → (e b : Bool) →
    (shift : Nat) →
    covarianceOrbitPrefix V depth t u m n e b shift ≡
    repeatRationalSum depth
      (stochasticCovariance (ensemble V) t u m n e b)
  covarianceOrbitPrefix-stationary V zero t u m n e b shift =
    refl
  covarianceOrbitPrefix-stationary V (suc depth) t u m n e b shift
    rewrite covarianceOrbitFromShift-head V t u m n e b shift =
      cong₂ _+ℚ_
        (covarianceAtShift-stationary V t u m n e b shift)
        (covarianceOrbitPrefix-stationary V depth t u m n e b
          (advanceCovarianceShift (timeAction V) shift))

  infiniteCovarianceHistory :
    {P : RationalPositivity} {samples times modes : Nat} →
    (V : FiniteSEDVacuumAxioms P samples times modes) →
    (t u : Nat) → (m n : Nat) → Bool → Bool →
    ConatStream Rational
  infiniteCovarianceHistory V t u m n e b =
    covarianceOrbitFromShift V t u m n e b (timeOrigin (timeAction V))

  infiniteCovariancePrefix :
    {P : RationalPositivity} {samples times modes : Nat} →
    (V : FiniteSEDVacuumAxioms P samples times modes) →
    Nat → (t u : Nat) → (m n : Nat) → Bool → Bool →
    Rational
  infiniteCovariancePrefix V depth t u m n e b =
    covarianceOrbitPrefix V depth t u m n e b
      (timeOrigin (timeAction V))

  ----------------------------------------------------------------------
  -- Exact rational Cayley evolution of each stochastic normal mode.
  -- For h = omega*dt, the oscillator rotation has
  -- c=(4-h²)/(4+h²), s=4h/(4+h²).  Cross multiplication keeps all
  -- equations inside the rational ring and the positive denominator proof
  -- makes the update domain explicit.  The energy law is part of the
  -- certificate and can be checked against any concrete finite trajectory.
  ----------------------------------------------------------------------

  fourRational : Rational
  fourRational = twice +ℚ twice

  record RationalCayleyModeStep
    (P : RationalPositivity)
    (omega dt electricBefore magneticBefore electricAfter magneticAfter : Rational)
    : Set₁ where
    field
      scaledFrequency : Rational
      scaledFrequencyLaw : scaledFrequency ≡ (omega *ℚ dt)
      denominator : Rational
      denominatorLaw : denominator ≡
        (fourRational +ℚ (scaledFrequency *ℚ scaledFrequency))
      denominatorPositive : Positive P denominator
      electricNumeratorEquation :
        (denominator *ℚ electricAfter) ≡
        (((fourRational -ℚ (scaledFrequency *ℚ scaledFrequency)) *ℚ
          electricBefore) +ℚ
         ((fourRational *ℚ scaledFrequency) *ℚ magneticBefore))
      magneticNumeratorEquation :
        (denominator *ℚ magneticAfter) ≡
        (((0ℚ -ℚ (fourRational *ℚ scaledFrequency)) *ℚ
          electricBefore) +ℚ
         ((fourRational -ℚ (scaledFrequency *ℚ scaledFrequency)) *ℚ
          magneticBefore))
      oscillatorEnergyPreserved :
        ((electricAfter *ℚ electricAfter) +ℚ
         (magneticAfter *ℚ magneticAfter)) ≡
        ((electricBefore *ℚ electricBefore) +ℚ
         (magneticBefore *ℚ magneticBefore))
  open RationalCayleyModeStep public

  ----------------------------------------------------------------------
  -- CONSTRUCTIVE FINITE MODE EVALUATOR
  --
  -- Exact Cayley update as numerator/denominator pairs.  This evaluator
  -- computes the finite rational step without floating-point trigonometry
  -- or a partial division operation.  The caller supplies the proof that
  -- the common denominator is nonzero.
  ----------------------------------------------------------------------

  cayleyModeDenominator : Rational → Rational
  cayleyModeDenominator h =
    fourRational +ℚ (h *ℚ h)

  cayleyModeElectricNumerator :
    Rational → Rational → Rational → Rational
  cayleyModeElectricNumerator h electric magnetic =
    ((fourRational -ℚ (h *ℚ h)) *ℚ electric) +ℚ
    ((fourRational *ℚ h) *ℚ magnetic)

  cayleyModeMagneticNumerator :
    Rational → Rational → Rational → Rational
  cayleyModeMagneticNumerator h electric magnetic =
    ((0ℚ -ℚ (fourRational *ℚ h)) *ℚ electric) +ℚ
    ((fourRational -ℚ (h *ℚ h)) *ℚ magnetic)

  record RationalCayleyModeFractions : Set where
    constructor rationalCayleyModeFractions
    field
      electricResultFraction : RationalFraction
      magneticResultFraction : RationalFraction
  open RationalCayleyModeFractions public

  evaluateRationalCayleyMode :
    (omega dt electric magnetic : Rational) →
    Nonzero (cayleyModeDenominator (omega *ℚ dt)) →
    RationalCayleyModeFractions
  evaluateRationalCayleyMode omega dt electric magnetic denominatorProof =
    let h = omega *ℚ dt
        denominator = cayleyModeDenominator h
    in rationalCayleyModeFractions
      (fraction
        (cayleyModeElectricNumerator h electric magnetic)
        denominator denominatorProof)
      (fraction
        (cayleyModeMagneticNumerator h electric magnetic)
        denominator denominatorProof)

  -- Exact polynomial residual of the oscillator energy identity.  It is
  -- computed, never silently cancelled.  Its vanishing is an explicit
  -- proof obligation for a concrete lawful rational instance.
  cayleyModeNumeratorEnergy :
    (h electric magnetic : Rational) → Rational
  cayleyModeNumeratorEnergy h electric magnetic =
    (cayleyModeElectricNumerator h electric magnetic *ℚ
     cayleyModeElectricNumerator h electric magnetic) +ℚ
    (cayleyModeMagneticNumerator h electric magnetic *ℚ
     cayleyModeMagneticNumerator h electric magnetic)

  cayleyModeDenominatorEnergy :
    (h electric magnetic : Rational) → Rational
  cayleyModeDenominatorEnergy h electric magnetic =
    (cayleyModeDenominator h *ℚ cayleyModeDenominator h) *ℚ
    ((electric *ℚ electric) +ℚ (magnetic *ℚ magnetic))

  cayleyModeEnergyResidual :
    (h electric magnetic : Rational) → Rational
  cayleyModeEnergyResidual h electric magnetic =
    cayleyModeNumeratorEnergy h electric magnetic -ℚ
    cayleyModeDenominatorEnergy h electric magnetic

  record VerifiedRationalCayleyModeFractions
    (omega dt electric magnetic : Rational)
    (denominatorProof :
      Nonzero (cayleyModeDenominator (omega *ℚ dt))) : Set₁ where
    field
      fractions : RationalCayleyModeFractions
      fractionsAreComputed :
        fractions ≡ evaluateRationalCayleyMode
          omega dt electric magnetic denominatorProof
      exactEnergyResidualZero :
        cayleyModeEnergyResidual (omega *ℚ dt) electric magnetic ≡ 0ℚ
  open VerifiedRationalCayleyModeFractions public

  ----------------------------------------------------------------------
  -- 5. RECONSTRUCTION OF STOCHASTIC ELECTROMAGNETIC FIELDS
  --
  -- A finite mode basis maps stochastic mode amplitudes into actual spatial
  -- electric 1-cochains and magnetic 2-cochains.  The basis obeys Maxwell's
  -- discrete curl eigen-relations.  No continuum Lorentz-invariance claim
  -- is made by this finite-band representation.
  ----------------------------------------------------------------------

  record MaxwellModeBasis
    {P : RationalPositivity}
    (H : MetricHodgeComplex P) (modes : Nat)
    (frequency : Nat → Rational) : Set₁ where
    field
      electricMode : Nat → Cochain (n₁ (complex H))
      magneticMode : Nat → Cochain (n₂ (complex H))
      modeFaraday : (m : Nat) →
        _≡_
          (d₁ (complex H) (electricMode m))
          (scaleCochain (frequency m) (magneticMode m))
      modeAmpere : (m : Nat) →
        _≡_
          (δ₂ H (magneticMode m))
          (scaleCochain (frequency m) (electricMode m))
  open MaxwellModeBasis public

  sumCochain :
    {n : Nat} → (k : Nat) → (Nat → Cochain n) → Cochain n
  sumCochain zero f = zeroCochain
  sumCochain (suc k) f =
    addCochain (f zero) (sumCochain k (λ i → f (suc i)))

  sampleElectricField :
    {P : RationalPositivity} {samples times modes : Nat} →
    {frequency : Nat → Rational} →
    (H : MetricHodgeComplex P) →
    (B : MaxwellModeBasis H modes frequency) →
    (N : FiniteSEDEnsemble P samples times modes) →
    Nat → Nat → Cochain (n₁ (complex H))
  sampleElectricField {modes = modes} H B N w t =
    sumCochain modes (λ m →
      scaleCochain (electricAmplitude N w t m) (electricMode B m))

  sampleMagneticField :
    {P : RationalPositivity} {samples times modes : Nat} →
    {frequency : Nat → Rational} →
    (H : MetricHodgeComplex P) →
    (B : MaxwellModeBasis H modes frequency) →
    (N : FiniteSEDEnsemble P samples times modes) →
    Nat → Nat → Cochain (n₂ (complex H))
  sampleMagneticField {modes = modes} H B N w t =
    sumCochain modes (λ m →
      scaleCochain (magneticAmplitude N w t m) (magneticMode B m))

  ----------------------------------------------------------------------
  -- 6. FINITE SED VACUUM-MAXWELL WORLD
  --
  -- This is the source-free zero-point background sector. Charged particle
  -- deposition, self-consistent source current, and recoil are a separate
  -- coupled-matter layer and are not claimed by this record.
  ----------------------------------------------------------------------

  record FiniteSEDVacuumMaxwellWorld
    (P : RationalPositivity)
    (samples times modes : Nat) : Set₃ where
    field
      hodgeMaxwell : MetricHodgeComplex P
      zpfVacuum : FiniteSEDVacuumAxioms P samples times modes
      modeBasis : MaxwellModeBasis hodgeMaxwell modes
        (modeFrequency zpfVacuum)
      timeStepSize : Rational
      timeStepPositive : Positive P timeStepSize
      sampleState : Nat → Nat → MaxwellState hodgeMaxwell
      sampleModeCayleyTransition :
        (w : Nat) (t : Nat) (m : Nat) →
        RationalCayleyModeStep P
          (modeFrequency zpfVacuum m) timeStepSize
          (electricAmplitude (ensemble zpfVacuum) w t m)
          (magneticAmplitude (ensemble zpfVacuum) w t m)
          (electricAmplitude (ensemble zpfVacuum) w
            (nextTime (timeAction zpfVacuum) t) m)
          (magneticAmplitude (ensemble zpfVacuum) w
            (nextTime (timeAction zpfVacuum) t) m)
      sampleFieldMatchesElectricModes :
        (w : Nat) (t : Nat) →
        _≡_
          (electricField (sampleState w t))
          (sumCochain modes
            (λ m → scaleCochain
              (electricAmplitude (ensemble zpfVacuum) w t m)
              (electricMode modeBasis m)))
      sampleFieldMatchesMagneticModes :
        (w : Nat) (t : Nat) →
        _≡_
          (magneticField (sampleState w t))
          (sumCochain modes
            (λ m → scaleCochain
              (magneticAmplitude (ensemble zpfVacuum) w t m)
              (magneticMode modeBasis m)))
      sampleVacuumChargeFree : (w : Nat) (t : Nat) →
        _≡_ (chargeDensity (sampleState w t)) zeroCochain
      sampleElectricHodgeSplit : (w : Nat) (t : Nat) →
        HodgeDecomposition₁ hodgeMaxwell (electricField (sampleState w t))
      sampleMagneticHodgeSplit : (w : Nat) (t : Nat) →
        HodgeDecomposition₂ hodgeMaxwell (magneticField (sampleState w t))
      sampleMaxwellTransition :
        (w : Nat) (t : Nat) →
        MaxwellMidpointStep hodgeMaxwell timeStepSize zeroCochain
          (sampleState w t)
          (sampleState w (nextTime (timeAction zpfVacuum) t))
      initialMomentum : Exchange.ClosedMomentumSnapshot
      momentumExchanges : List Exchange.MomentumExchange
      euclideanLaws : RationalTrigonometryLawWitness
  open FiniteSEDVacuumMaxwellWorld public

  ----------------------------------------------------------------------
  -- 7. DERIVED CERTIFICATE BUNDLE OVER THE COMPLETE FINITE WORLD
  --
  -- This is deliberately downstream of the axiom input. It packages
  -- finite consequences and world-specific certificates; it is not part
  -- of the SED axiom list. It is indexed by the complete world value.
  ----------------------------------------------------------------------

  record FiniteSEDVacuumMotive
    (P : RationalPositivity)
    (samples times modes : Nat)
    (W : FiniteSEDVacuumMaxwellWorld P samples times modes) : Set₁ where
    field
      probabilityNormalization :
        sumFinite samples (probabilityWeight (ensemble (zpfVacuum W))) ≡ 1ℚ
      electricMeanZero : (t : Nat) (m : Nat) →
        stochasticMean (ensemble (zpfVacuum W)) t m true ≡ 0ℚ
      magneticMeanZero : (t : Nat) (m : Nat) →
        stochasticMean (ensemble (zpfVacuum W)) t m false ≡ 0ℚ
      electricVarianceNonnegative : (t : Nat) (m : Nat) →
        Nonnegative P (stochasticCovariance (ensemble (zpfVacuum W))
          t t m m true true)
      magneticVarianceNonnegative : (t : Nat) (m : Nat) →
        Nonnegative P (stochasticCovariance (ensemble (zpfVacuum W))
          t t m m false false)
      covarianceStationarity :
        (t u s : Nat) (m n : Nat) (e b : Bool) →
        stochasticCovariance (ensemble (zpfVacuum W))
          (translateTime (timeAction (zpfVacuum W)) t s)
          (translateTime (timeAction (zpfVacuum W)) u s) m n e b ≡
        stochasticCovariance (ensemble (zpfVacuum W)) t u m n e b
      covarianceSymmetry : (t u : Nat) (m n : Nat) (e b : Bool) →
        stochasticCovariance (ensemble (zpfVacuum W)) t u m n e b ≡
        stochasticCovariance (ensemble (zpfVacuum W)) u t n m b e
      -- Executable access to finite prefixes of the conatural infinite
      -- stationary-translation covariance history.  No limit-existence axiom
      -- is implied: every requested prefix is computed by finite folding.
      conaturalCovariancePrefix :
        (depth : Nat) (t u : Nat) (m n : Nat) (e b : Bool) →
        Rational
      conaturalCovariancePrefixStationary :
        (depth : Nat) (t u : Nat) (m n : Nat) (e b : Bool) →
        (shift : Nat) →
        covarianceOrbitPrefix (zpfVacuum W) depth t u m n e b shift ≡
        repeatRationalSum depth
          (stochasticCovariance (ensemble (zpfVacuum W)) t u m n e b)
      zeroPointModeEnergy : (t : Nat) (m : Nat) →
        (stochasticCovariance (ensemble (zpfVacuum W)) t t m m true true +ℚ
         stochasticCovariance (ensemble (zpfVacuum W)) t t m m false false)
        ≡ (hbarScale (zpfVacuum W) *ℚ modeFrequency (zpfVacuum W) m)
      densityScaleCalibration :
        densityScale (zpfVacuum W) ≡
        (hbarScale (zpfVacuum W) *ℚ densityNormalization (zpfVacuum W))
      finiteBandSpectrum : (m : Nat) →
        spectralDensity (zpfVacuum W) m ≡
        (densityScale (zpfVacuum W) *ℚ
          (modeFrequency (zpfVacuum W) m *ℚ
           (modeFrequency (zpfVacuum W) m *ℚ modeFrequency (zpfVacuum W) m)))
      modeCayleyEvolution : (w : Nat) (t : Nat) (m : Nat) →
        RationalCayleyModeStep P
          (modeFrequency (zpfVacuum W) m) (timeStepSize W)
          (electricAmplitude (ensemble (zpfVacuum W)) w t m)
          (magneticAmplitude (ensemble (zpfVacuum W)) w t m)
          (electricAmplitude (ensemble (zpfVacuum W)) w
            (nextTime (timeAction (zpfVacuum W)) t) m)
          (magneticAmplitude (ensemble (zpfVacuum W)) w
            (nextTime (timeAction (zpfVacuum W)) t) m)
      electricHodge : (w : Nat) (t : Nat) →
        HodgeDecomposition₁ (hodgeMaxwell W)
          (electricField (sampleState W w t))
      magneticHodge : (w : Nat) (t : Nat) →
        HodgeDecomposition₂ (hodgeMaxwell W)
          (magneticField (sampleState W w t))
      vacuumMaxwellStep : (w : Nat) (t : Nat) →
        MaxwellMidpointStep (hodgeMaxwell W) (timeStepSize W) zeroCochain
          (sampleState W w t)
          (sampleState W w (nextTime (timeAction (zpfVacuum W)) t))
      totalMomentumConservation :
        Exchange.totalClosedMomentum
          (Exchange.runExchanges (momentumExchanges W) (initialMomentum W))
          ≡
        Exchange.totalClosedMomentum (initialMomentum W)
  open FiniteSEDVacuumMotive public

  assembleFiniteSEDVacuumMotive :
    {P : RationalPositivity} {samples times modes : Nat} →
    (W : FiniteSEDVacuumMaxwellWorld P samples times modes) →
    FiniteSEDVacuumMotive P samples times modes W
  assembleFiniteSEDVacuumMotive W = record
    { probabilityNormalization = normalizedWeights (ensemble (zpfVacuum W))
    ; electricMeanZero = meanZeroElectric (zpfVacuum W)
    ; magneticMeanZero = meanZeroMagnetic (zpfVacuum W)
    ; electricVarianceNonnegative = λ t m → stochasticVarianceNonnegative (ensemble (zpfVacuum W)) t m true
    ; magneticVarianceNonnegative = λ t m → stochasticVarianceNonnegative (ensemble (zpfVacuum W)) t m false
    ; covarianceStationarity = timeTranslationStationary (zpfVacuum W)
    ; covarianceSymmetry = stochasticCovariance-symmetric (ensemble (zpfVacuum W))
    ; conaturalCovariancePrefix = λ depth t u m n e b →
        infiniteCovariancePrefix (zpfVacuum W) depth t u m n e b
    ; conaturalCovariancePrefixStationary =
        covarianceOrbitPrefix-stationary (zpfVacuum W)
    ; zeroPointModeEnergy = modeEnergyCovariance (zpfVacuum W)
    ; densityScaleCalibration = densityScaleLaw (zpfVacuum W)
    ; finiteBandSpectrum = omegaCubedLaw (zpfVacuum W)
    ; modeCayleyEvolution = sampleModeCayleyTransition W
    ; electricHodge = sampleElectricHodgeSplit W
    ; magneticHodge = sampleMagneticHodgeSplit W
    ; vacuumMaxwellStep = sampleMaxwellTransition W
    ; totalMomentumConservation =
        Exchange.runExchanges-conserves (momentumExchanges W) (initialMomentum W)
    }


------------------------------------------------------------------------
-- End RSEDPhysicalFoundations
------------------------------------------------------------------------
