{-# OPTIONS
--erasure
--experimental-lazy-instances
--lossy-unification
--syntactic-equality=1
--no-eta-equality
--prop
--with-K
--no-fast-reduce
--no-projection-like
--erased-quotients
--erased-funext
--erased-propext
--auto-inline
--exact-split
--rewriting
--confluence-check
#-}

module FullCoupled.CanonicalLearnerMonolith where

------------------------------------------------------------------------
-- The small proof surface follows the relevant Agdalache patterns:
-- erased S0 witnesses, propositional equality, and relation support.
-- The learner has no C pointer, IORef, StablePtr, MVar, or CFuture API.
------------------------------------------------------------------------

-- Follow the standard Agda2HS base-library convention used in Viktor
-- Csimma's examples: Haskell.Prelude is the shared Agda/Haskell surface.
-- It re-exports equality, builtin Nat, products, and primitive proof types.
-- Vec's Nat index is erased, so no runtime length or Peano traversal remains.
open import Agda.Primitive using (Level; _⊔_)
open import Haskell.Prelude public
open import Agda.Builtin.Erased.Funext public
open import Agda.Builtin.Erased.Propext public
open import Agda.Builtin.Erased.Quotient public
open import Agda.Builtin.Equality.Rewrite public

------------------------------------------------------------------------
-- Erased proof packaging
------------------------------------------------------------------------

postulate
  S : Set
  F : Set → Set → Set
  G : (Set → Set) → Set → Set → Set
  rewF : (A : Set) → F A A ≡ S
  rewG : (A : Set → Set) (X Y : Set) → G A X Y ≡ F (A X) (A Y)
{-# REWRITE rewF rewG #-}

test : (A : Set → Set) → G A _ _
test A x = {!!}


record S0 {i j : Level} (A : Set i) (@0 P : A → Set j) : Set (i ⊔ j) where
  no-eta-equality
  constructor packS0
  field
    valueS0 : A
    @0 proofS0 : P valueS0

open S0 public
{-# COMPILE AGDA2HS S0 newtype #-}

∃0 : ∀ {i j} {A : Set i} → @0 (A → Set j) → Set (i ⊔ j)
∃0 {A = A} P = S0 A P
{-# COMPILE AGDA2HS ∃0 #-}

------------------------------------------------------------------------
-- Equality and relation support
------------------------------------------------------------------------

@0 cong
  : ∀ {i} {A B : Set i} (f : A → B) {x y : A}
  → x ≡ y → f x ≡ f y
cong f refl = refl

@0 sym : ∀ {i} {A : Set i} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

@0 trans
  : ∀ {i} {A : Set i} {x y z : A}
  → x ≡ y → y ≡ z → x ≡ z
trans refl yz = yz

@0 subst
  : ∀ {i} {A : Set i} {x y : A}
  → (P : A → Set) → x ≡ y → P x → P y
subst P refl px = px

infix 4 _≢_
_≢_ : ∀ {i} {A : Set i} → A → A → Set i
x ≢ y = (x ≡ y) → ⊥

data _⊎_ {i j : Level} (A : Set i) (B : Set j) : Set (i ⊔ j) where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

------------------------------------------------------------------------
-- Erased-length vectors
------------------------------------------------------------------------

data Vec (A : Set) : (@0 n : Nat) → Set where
  VNil  : Vec A zero
  VCons : ∀ {@0 n} → A → Vec A n → Vec A (suc n)

{-# COMPILE AGDA2HS Vec #-}

mapVec : ∀ {A B : Set} {@0 n} → (A → B) → Vec A n → Vec B n
mapVec f VNil = VNil
mapVec f (VCons x xs) = VCons (f x) (mapVec f xs)
{-# COMPILE AGDA2HS mapVec #-}

zipWithVec
  : ∀ {A B C : Set} {@0 n}
  → (A → B → C) → Vec A n → Vec B n → Vec C n
zipWithVec f VNil VNil = VNil
zipWithVec f (VCons x xs) (VCons y ys) =
  VCons (f x y) (zipWithVec f xs ys)
{-# COMPILE AGDA2HS zipWithVec #-}

------------------------------------------------------------------------
-- Q12.20 fixed-point representation
--
-- The Agda type is opaque. Its extracted representation is Data.Int.Int32.
-- Every arithmetic primitive widens to Int64, rounds ties to even, then
-- saturates to Int32. Division by zero is represented explicitly.
------------------------------------------------------------------------

{-# FOREIGN AGDA2HS
import Data.Int (Int32, Int64)

satInt32 :: Int64 -> Int32
satInt32 n
  | n < fromIntegral (minBound :: Int32) = minBound
  | n > fromIntegral (maxBound :: Int32) = maxBound
  | otherwise = fromIntegral n

roundDivEven :: Int64 -> Int64 -> Int64
roundDivEven n d =
  let (q, r) = quotRem n d
      twiceR = 2 * abs r
      absD = abs d
      step = signum n * signum d
  in case compare twiceR absD of
       LT -> q
       GT -> q + step
       EQ -> if even q then q else q + step

int32Zero :: Int32
int32Zero = 0

int32OneQ20 :: Int32
int32OneQ20 = 1048576

addInt32 :: Int32 -> Int32 -> Int32
addInt32 x y = satInt32 (fromIntegral x + fromIntegral y)

subInt32 :: Int32 -> Int32 -> Int32
subInt32 x y = satInt32 (fromIntegral x - fromIntegral y)

mulQ20Int32 :: Int32 -> Int32 -> Int32
mulQ20Int32 x y =
  satInt32 (roundDivEven (fromIntegral x * fromIntegral y) 1048576)

negInt32 :: Int32 -> Int32
negInt32 x = satInt32 (negate (fromIntegral x))

absInt32 :: Int32 -> Int32
absInt32 x = satInt32 (abs (fromIntegral x))

divQ20Int32 :: Int32 -> Int32 -> Div32Result
divQ20Int32 _ 0 = Div32ByZero
divQ20Int32 x y =
  Div32Quotient
    (satInt32
      (roundDivEven (fromIntegral x * 1048576) (fromIntegral y)))
#-}

postulate
  Int32 : Set
  int32Zero : Int32
  int32OneQ20 : Int32
  addInt32 : Int32 → Int32 → Int32
  subInt32 : Int32 → Int32 → Int32
  mulQ20Int32 : Int32 → Int32 → Int32
  negInt32 : Int32 → Int32
  absInt32 : Int32 → Int32

{-# COMPILE AGDA2HS int32Zero #-}
{-# COMPILE AGDA2HS int32OneQ20 #-}
{-# COMPILE AGDA2HS addInt32 #-}
{-# COMPILE AGDA2HS subInt32 #-}
{-# COMPILE AGDA2HS mulQ20Int32 #-}
{-# COMPILE AGDA2HS negInt32 #-}
{-# COMPILE AGDA2HS absInt32 #-}

data Div32Result : Set where
  Div32ByZero : Div32Result
  Div32Quotient : Int32 → Div32Result

{-# COMPILE AGDA2HS Div32Result #-}

postulate
  divQ20Int32 : Int32 → Int32 → Div32Result

{-# COMPILE AGDA2HS divQ20Int32 #-}

record Q20 : Set where
  constructor MkQ20
  field
    rawQ20 : Int32

open Q20 public
{-# COMPILE AGDA2HS Q20 newtype #-}

data Q20DivResult : Set where
  Q20DivByZero : Q20DivResult
  Q20DivValue : Q20 → Q20DivResult

{-# COMPILE AGDA2HS Q20DivResult #-}

q20Zero : Q20
q20Zero = MkQ20 int32Zero
{-# COMPILE AGDA2HS q20Zero #-}

q20One : Q20
q20One = MkQ20 int32OneQ20
{-# COMPILE AGDA2HS q20One #-}

q20Add : Q20 → Q20 → Q20
q20Add (MkQ20 x) (MkQ20 y) = MkQ20 (addInt32 x y)
{-# COMPILE AGDA2HS q20Add #-}

q20Sub : Q20 → Q20 → Q20
q20Sub (MkQ20 x) (MkQ20 y) = MkQ20 (subInt32 x y)
{-# COMPILE AGDA2HS q20Sub #-}

q20Mul : Q20 → Q20 → Q20
q20Mul (MkQ20 x) (MkQ20 y) = MkQ20 (mulQ20Int32 x y)
{-# COMPILE AGDA2HS q20Mul #-}

q20Neg : Q20 → Q20
q20Neg (MkQ20 x) = MkQ20 (negInt32 x)
{-# COMPILE AGDA2HS q20Neg #-}

q20Abs : Q20 → Q20
q20Abs (MkQ20 x) = MkQ20 (absInt32 x)
{-# COMPILE AGDA2HS q20Abs #-}

q20Div : Q20 → Q20 → Q20DivResult
q20Div (MkQ20 x) (MkQ20 y) with divQ20Int32 x y
... | Div32ByZero = Q20DivByZero
... | Div32Quotient z = Q20DivValue (MkQ20 z)
{-# COMPILE AGDA2HS q20Div #-}

Q20Pair : Set
Q20Pair = Q20 × Q20
{-# COMPILE AGDA2HS Q20Pair #-}
