{-# OPTIONS --erasure #-}

module Compat.Data.Bits where

open import Haskell.Prelude
open import Compat.Data.Int using (quot)

private
  powerOfTwo : Nat → Int
  powerOfTwo zero = 1
  powerOfTwo (suc amount) = 2 * powerOfTwo amount

shiftL : Int → Nat → Int
shiftL value amount =
  if amount < 64 then value * powerOfTwo amount else 0
{-# COMPILE AGDA2HS shiftL #-}

-- Arithmetic right shift: negative values round toward negative infinity,
-- matching signed two's-complement shift semantics.
shiftR : Int → Nat → Int
shiftR value amount with amount < 64 | value < 0
... | False | False = 0
... | False | True = -1
... | True | False = quot value (powerOfTwo amount)
... | True | True =
  negate
    (quot
      (negate value + powerOfTwo amount - 1)
      (powerOfTwo amount))
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
