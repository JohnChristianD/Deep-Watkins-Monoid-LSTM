{-# OPTIONS --exact-split --rewriting --confluence-check #-}

------------------------------------------------------------------------
-- Minimal axiomatized circle interface, isolated from the legacy
-- --with-K / --sized-types monolith.
--
-- Only the point and loop computation laws for the dependent eliminator are
-- supplied. This is an ordinary Agda postulate/rewrite interface, not native
-- kernel-level HIT support and not a Cubical implementation.
------------------------------------------------------------------------

module FullCoupled.CircleHITInterface where

open import Agda.Primitive using (Level)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Equality.Rewrite

transport :
  {A : Set} {ℓ : Level} →
  (P : A → Set ℓ) → {x y : A} → x ≡ y → P x → P y
transport P refl value = value

apd :
  {A : Set} {ℓ : Level} {P : A → Set ℓ} {x y : A} →
  (f : (x : A) → P x) → (p : x ≡ y) →
  transport P p (f x) ≡ f y
apd f refl = refl

postulate
  Circle : Set
  base : Circle
  loop : base ≡ base

-- The dependent eliminator carries the loop's transported coherence as input.
postulate
  Circle-elim :
    {ℓ : Level} (P : Circle → Set ℓ) →
    (base* : P base) →
    (loop* : transport P loop base* ≡ base*) →
    (x : Circle) → P x

  Circle-elim-base :
    {ℓ : Level} (P : Circle → Set ℓ) (base* : P base)
    (loop* : transport P loop base* ≡ base*) →
    Circle-elim P base* loop* base ≡ base*

-- Register the point computation before declaring the path computation: the
-- latter's expected type reduces to the supplied loop coherence only after
-- this specific equation has entered definitional equality.
{-# REWRITE Circle-elim-base #-}

postulate
  Circle-elim-loop :
    {ℓ : Level} (P : Circle → Set ℓ) (base* : P base)
    (loop* : transport P loop base* ≡ base*) →
    apd (Circle-elim P base* loop*) loop ≡ loop*

{-# REWRITE Circle-elim-loop #-}
