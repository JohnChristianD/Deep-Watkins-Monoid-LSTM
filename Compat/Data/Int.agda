{-# OPTIONS --erasure #-}

module Compat.Data.Int where

open import Haskell.Prim using (monusNat)
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

divideNat : Nat → Nat → Nat
divideNat numerator denominator =
  if denominator == 0
  then 0
  else div-helper 0 (monusNat denominator 1) numerator (monusNat denominator 1)
{-# COMPILE AGDA2HS divideNat #-}

negativeMagnitude : Nat → Integer
negativeMagnitude magnitude =
  if magnitude == 0
  then pos 0
  else negsuc (monusNat magnitude 1)
{-# COMPILE AGDA2HS negativeMagnitude #-}

quotientInteger : Integer → Integer → Integer
quotientInteger (pos numerator) (pos denominator) =
  if denominator == 0
  then pos 0
  else pos (divideNat numerator denominator)
quotientInteger (pos numerator) (negsuc denominator) =
  negativeMagnitude (divideNat numerator (denominator + 1))
quotientInteger (negsuc numerator) (pos denominator) =
  if denominator == 0
  then pos 0
  else negativeMagnitude (divideNat (numerator + 1) denominator)
quotientInteger (negsuc numerator) (negsuc denominator) =
  pos (divideNat (numerator + 1) (denominator + 1))
{-# COMPILE AGDA2HS quotientInteger #-}

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
