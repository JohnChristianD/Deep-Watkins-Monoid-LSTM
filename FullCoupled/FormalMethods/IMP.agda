{-# OPTIONS
  --lossy-unification
  --backtracking-instance-search
  --experimental-lazy-instances
  --confluence-check
  --polarity
  --auto-inline
  --guarded
  --exact-split
  --no-infer-absurd-clauses
  --keep-covering-clauses
  --no-projection-like
  --erasure
#-}


------------------------------------------------------------------------
-- Vendored from iwilare/formal-methods (IMP.agda), MIT-licensed upstream.
-- Namespaced locally so theorem-specific imports cannot collide with the
-- existing FullCoupled proof surface.
------------------------------------------------------------------------

module FullCoupled.FormalMethods.IMP where

-- Merged external import surface; internal FullCoupled imports remain module-local.
open import Haskell.Prelude hiding (String; ⊥)
open import MLTT.Spartan hiding (J)
open import Naturals
open import Naturals.Exponentiation
open import Naturals.Division
open import Naturals.Properties
open import Notation.Order
open import Order
open import Rationals.Addition
open import Rationals.Multiplication
open import Rationals.Negation
open import Rationals.Order
open import Rationals.Type
open import UF.Base
open import UF.FunExt
open import UF.PropTrunc
open import UF.Size
open import UF.Subsingletons
open import UF.Subsingletons-FunExt
open import UF.UA-FunExt



vname = String
val = Nat
bool = Bool
state = vname → val

data aexp : Set where
  N : Nat → aexp
  V : vname → aexp
  Plus : aexp → aexp → aexp

_[_/_] : aexp → aexp → vname → aexp
N c [ a′ / X ] = N c
V Y [ a′ / X ] with Y ≟ X
... | yes _ = a′
... | no  _ = V Y
Plus a b [ a′ / X ] = Plus (a [ a′ / X ]) (b [ a′ / X ])

_[_::=_] : state → vname → val → state
(s [ X ::= n ]) Y with Y ≟ X
... | yes _ = n
... | no  _ = s Y

aval : aexp → state → val
aval (N c) s = c
aval (V v) s = s v
aval (Plus a b) s = aval a s + aval b s

substitution : ∀ a {X a′ s}
  → aval (a [ a′ / X ]) s ≡ aval a (s [ X ::= aval a′ s ])
substitution (N x) = refl
substitution (V Y) {X} with Y ≟ X
... | yes _ = refl
... | no  _ = refl
substitution (Plus a b) {X}{a′}{s}
  rewrite substitution a {X}{a′}{s}
        | substitution b {X}{a′}{s} = refl

substitution-equiv : ∀{a a₁ a₂ X s}
  → aval a₁ s             ≡ aval a₂ s
  → aval (a [ a₁ / X ]) s ≡ aval (a [ a₂ / X ]) s
substitution-equiv {a}{a₁}{a₂}{X}{s} hyp
  rewrite substitution a {X}{a₁}{s}
        | hyp
        | sym (substitution a {X}{a₂}{s}) = refl

data bexp : Set where
  Bc   : Bool → bexp
  Not  : bexp → bexp
  And  : bexp → bexp → bexp
  Less : aexp → aexp → bexp

_≤?_ : Nat → Nat → Bool
a ≤? b = a ≤?ₙ b

bval : bexp → state → bool
bval (Bc x) s = x
bval (Not b) s = not (bval b s)
bval (And a b) s = bval a s ∧ bval b s
bval (Less a b) s = aval a s ≤? aval b s

data com : Set where
  SKIP  : com
  _::=_ : String → aexp → com
  _::_  : com → com → com
  IF_THEN_ELSE_ : bexp → com → com → com
  WHILE_DO_     : bexp → com → com
