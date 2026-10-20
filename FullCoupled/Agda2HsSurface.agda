module FullCoupled.Agda2HsSurface where


open import Haskell.Prelude

record Counter : Type where
  no-eta-equality; pattern
  constructor MkCounter
  field
    totalCount : Nat

open Counter public

stepCounter : Counter -> Counter
stepCounter (MkCounter n) = MkCounter (n + 1)

counterLaw : ∀ c -> Counter.totalCount (stepCounter c) ≡ Counter.totalCount c + 1
counterLaw (MkCounter n) = refl

{-# COMPILE AGDA2HS Counter #-}
{-# COMPILE AGDA2HS stepCounter #-}
