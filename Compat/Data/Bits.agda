{-# OPTIONS --erasure #-}

module Compat.Data.Bits where

open import Haskell.Prelude
open import Compat.Data.Int using (quot)

open import Haskell.Prim using (eqNat; monusNat)

powerOfTwo : Nat → Int
{-# TERMINATING #-}
powerOfTwo amount =
  if eqNat amount 0
  then 1
  else 2 * powerOfTwo (monusNat amount 1)
{-# COMPILE AGDA2HS powerOfTwo #-}

shiftL : Int → Nat → Int
shiftL value amount =
  if amount < 64 then value * powerOfTwo amount else 0
{-# COMPILE AGDA2HS shiftL #-}

-- Arithmetic right shift: negative values round toward negative infinity,
-- matching signed two's-complement shift semantics.
shiftR : Int → Nat → Int
shiftR value amount =
  if amount < 64
  then if value < 0
       then negate
         (quot
           (negate value + powerOfTwo amount - 1)
           (powerOfTwo amount))
       else quot value (powerOfTwo amount)
  else if value < 0 then -1 else 0
{-# COMPILE AGDA2HS shiftR #-}

private
  shiftNegativeRoundsDown : shiftR (-3) 1 ≡ -2
  shiftNegativeRoundsDown = refl

  shiftPositiveRoundsDown : shiftR 3 1 ≡ 1
  shiftPositiveRoundsDown = refl

  shiftNegativeByWordWidth : shiftR (-3) 64 ≡ -1
  shiftNegativeByWordWidth = refl

  shiftPositiveByWordWidth : shiftR 3 64 ≡ 0
  shiftPositiveByWordWidth = refl

  shiftLeftByWordWidth : shiftL 3 64 ≡ 0
  shiftLeftByWordWidth = refl
