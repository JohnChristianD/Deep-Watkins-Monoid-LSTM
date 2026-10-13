module FullCoupled.Agda2HsSurface where


open import Haskell.Prelude

record Counter : Type where
  constructor counter
  field
    totalCount : Nat

stepCounter : Counter -> Counter
stepCounter (counter n) = counter (n + 1)

counterLaw : ∀ c -> Counter.totalCount (stepCounter c) ≡ Counter.totalCount c + 1
counterLaw (counter n) = refl

{-# COMPILE AGDA2HS Counter #-}
{-# COMPILE AGDA2HS stepCounter #-}
