{-# OPTIONS --erasure #-}

module Compat.Data.Int where

open import Haskell.Prim using (monusNat; div-helper; pos; negsuc)
open import Haskell.Prelude
open import Haskell.Prim.Int using (absInt; unsafeIntToNat; integerToInt)

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

quot : Int64 → Int64 → Int64
quot numerator denominator =
  if denominator == 0
  then 0
  else
    let magnitude =
          divideNat
            (unsafeIntToNat (absInt numerator))
            (unsafeIntToNat (absInt denominator))
    in if magnitude == 0
       then 0
       else if (numerator < 0) == (denominator < 0)
            then integerToInt (pos magnitude)
            else integerToInt (negsuc (monusNat magnitude 1))
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
