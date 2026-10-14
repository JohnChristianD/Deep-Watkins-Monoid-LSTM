{-# OPTIONS --safe #-}

module FullCoupled.FormalMethods.ScottStracheyDomains where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Empty using (⊥)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)

-- A strict Scott-style lift. bottom denotes an undefined computation;
-- defined zero is a numeric value and is not the least element.
data Lift (A : Set) : Set where
  bottom : Lift A
  defined : A → Lift A

infix 4 _⊑_

-- Flat-domain order: bottom lies below every value; defined values are
-- comparable only with themselves.
data _⊑_ {A : Set} : Lift A → Lift A → Set where
  bottomLeast : {value : Lift A} → bottom ⊑ value
  definedReflexive : {value : A} → defined value ⊑ defined value

reflexive⊑ : {A : Set} {value : Lift A} → value ⊑ value
reflexive⊑ {value = bottom} = bottomLeast
reflexive⊑ {value = defined value} = definedReflexive

bottomIsLeast : {A : Set} (value : Lift A) → bottom ⊑ value
bottomIsLeast _ = bottomLeast

-- This order fact is not an equality with numeric zero:
-- bottom ⊑ every value, but defined zero is an ordinary, defined value.
bottomIsNotZero : bottom ≡ defined zero → ⊥
bottomIsNotZero ()

definedZeroIsNotBottom : defined zero ≡ bottom → ⊥
definedZeroIsNotBottom ()

definedZeroIsNotLeast : defined zero ⊑ bottom → ⊥
definedZeroIsNotLeast ()

-- A tiny Scott–Strachey denotational semantics for numerals, divergence,
-- and strict addition.
data NatExpr : Set where
  numeral : Nat → NatExpr
  diverges : NatExpr
  _⊕_ : NatExpr → NatExpr → NatExpr

infixl 6 _⊕_

strictNatAdd : Lift Nat → Lift Nat → Lift Nat
strictNatAdd bottom _ = bottom
strictNatAdd (defined _) bottom = bottom
strictNatAdd (defined left) (defined right) = defined (left + right)

denote : NatExpr → Lift Nat
denote (numeral n) = defined n
denote diverges = bottom
denote (left ⊕ right) = strictNatAdd (denote left) (denote right)

definedAdditionRegression :
  denote (numeral 2 ⊕ numeral 3) ≡ defined (suc (suc (suc (suc (suc zero)))))
definedAdditionRegression = refl

divergenceAbsorbsAddition :
  denote (diverges ⊕ numeral 3) ≡ bottom
divergenceAbsorbsAddition = refl

record AlgebraOperations (A : Set) : Set₁ where
  field
    algebraZero : A
    algebraAdd : A → A → A
    algebraMultiply : A → A → A
    algebraNegate : A → A

open AlgebraOperations public

module StrictLiftedAlgebra {A : Set} (operations : AlgebraOperations A) where
  open AlgebraOperations operations

  strictAdd : Lift A → Lift A → Lift A
  strictAdd bottom _ = bottom
  strictAdd (defined _) bottom = bottom
  strictAdd (defined left) (defined right) =
    defined (algebraAdd left right)

  strictMultiply : Lift A → Lift A → Lift A
  strictMultiply bottom _ = bottom
  strictMultiply (defined _) bottom = bottom
  strictMultiply (defined left) (defined right) =
    defined (algebraMultiply left right)

  strictNegate : Lift A → Lift A
  strictNegate bottom = bottom
  strictNegate (defined value) = defined (algebraNegate value)

  -- This counterexample is about strict lifting, not about the unlifted A.
  inverseLawFailsAtBottom :
    strictAdd bottom (strictNegate bottom) ≡ defined algebraZero → ⊥
  inverseLawFailsAtBottom ()

  -- Strict multiplication does not make defined zero annihilate bottom.
  -- So strict lifted operations do not form a ring/semiring on all of Lift A.
  zeroAnnihilatorFailsAtBottom :
    strictMultiply (defined algebraZero) bottom ≡ defined algebraZero → ⊥
  zeroAnnihilatorFailsAtBottom ()
