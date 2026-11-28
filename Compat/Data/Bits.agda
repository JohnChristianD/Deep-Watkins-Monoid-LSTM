{-# OPTIONS --erasure #-}

module Compat.Data.Bits where

open import Haskell.Prelude
open import Compat.Data.Int using (quot)

{-# FOREIGN AGDA2HS
import qualified Data.Bits as Bits
import Data.Word (Word64)
import Numeric.Natural (Natural)
import qualified Haskell.Prim.Int as PrimInt
import qualified Prelude as P

powerOfTwoHaskell :: Natural -> PrimInt.Int
powerOfTwoHaskell amount =
  PrimInt.int64 (Bits.shiftL (1 :: Word64) (P.fromIntegral amount))
#-}

powerOfTwo : Nat → Int
powerOfTwo zero = 1
powerOfTwo (suc amount) = 2 * powerOfTwo amount
{-# COMPILE AGDA2HS powerOfTwo to powerOfTwoHaskell #-}

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
