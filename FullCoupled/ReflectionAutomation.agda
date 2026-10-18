{-# OPTIONS --without-K #-}

------------------------------------------------------------------------
-- Reflection helper for proof obligations that are definitionally reflexive.
--
-- The macro generates only `refl` and asks Agda's type checker to unify
-- it with the supplied goal. It introduces no postulate, proves no arbitrary
-- propositional equality, and fails if the goal does not reduce to reflexivity.
-- Keep Reflection qualified: opening the full AST exports names such as
-- `Type` and `abs` that collide with this repository's prelude.
------------------------------------------------------------------------

module FullCoupled.ReflectionAutomation where

open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.Equality using (_≡_; refl)
import Agda.Builtin.Reflection as Reflection

macro
  byDefinitionalRefl : Reflection.Term → Reflection.TC ⊤
  byDefinitionalRefl goal = Reflection.unify goal (quoteTerm refl)

-- A small compile-time regression: the β-reduction makes this equality
-- definitional, so the macro solves it without a handwritten proof clause.
identityBeta :
  {A : Set} (x : A) → ((λ y → y) x) ≡ x
identityBeta x = byDefinitionalRefl
