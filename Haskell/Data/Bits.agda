module Haskell.Data.Bits where

open import Haskell.Prelude
open import Haskell.Data.Int using (quot)

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
shiftR value amount =
  if amount < 64
  then
    let divisor = powerOfTwo amount
    in if value < 0
       then negate (quot (negate value + divisor - 1) divisor)
       else quot value divisor
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
