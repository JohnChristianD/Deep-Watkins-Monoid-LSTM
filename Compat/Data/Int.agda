{-# OPTIONS --erasure #-}

module Compat.Data.Int where

open import Haskell.Prelude
open import Haskell.Prim using (div-helper; pos; negsuc)

-- Both names use the base library's signed 64-bit carrier. The learner
-- enforces the narrower Q8.24 range whenever it narrows through qFrom64.
Int32 : Type
Int32 = Int
{-# COMPILE AGDA2HS Int32 #-}

Int64 : Type
Int64 = Int
{-# COMPILE AGDA2HS Int64 #-}

fromIntegral : Int32 → Int64
fromIntegral value = value
{-# COMPILE AGDA2HS fromIntegral #-}

private
  divideNat : Nat → Nat → Nat
  divideNat _ zero = zero
  divideNat numerator (suc denominator) =
    div-helper zero denominator numerator denominator

  negativeMagnitude : Nat → Integer
  negativeMagnitude zero = pos zero
  negativeMagnitude (suc magnitude) = negsuc magnitude

  quotientInteger : Integer → Integer → Integer
  quotientInteger (pos numerator) (pos zero) = pos zero
  quotientInteger (pos numerator) (pos (suc denominator)) =
    pos (divideNat numerator (suc denominator))
  quotientInteger (pos numerator) (negsuc denominator) =
    negativeMagnitude (divideNat numerator (suc denominator))
  quotientInteger (negsuc numerator) (pos zero) = pos zero
  quotientInteger (negsuc numerator) (pos (suc denominator)) =
    negativeMagnitude (divideNat (suc numerator) (suc denominator))
  quotientInteger (negsuc numerator) (negsuc denominator) =
    pos (divideNat (suc numerator) (suc denominator))

quot : Int64 → Int64 → Int64
quot numerator denominator =
  integerToInt
    (quotientInteger
      (intToInteger numerator)
      (intToInteger denominator))
{-# COMPILE AGDA2HS quot #-}

private
  quotientPositive : quot 7 3 ≡ 2
  quotientPositive = refl

  quotNegativeNumeratorTruncatesTowardZero : quot (-7) 3 ≡ -2
  quotNegativeNumeratorTruncatesTowardZero = refl

  quotNegativeDenominatorTruncatesTowardZero : quot 7 (-3) ≡ -2
  quotNegativeDenominatorTruncatesTowardZero = refl

  quotBothNegative : quot (-7) (-3) ≡ 2
  quotBothNegative = refl

  quotZeroDenominator : quot 7 0 ≡ 0
  quotZeroDenominator = refl
