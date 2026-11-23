------------------------------------------------------------------------
-- Pure fixed-point learner kernel.
-- Recurrent state is explicit input/output; Lua owns orchestration only.
------------------------------------------------------------------------

open import Haskell.Prelude public
open import Haskell.Data.Int public
open import Haskell.Data.Bits public

-- Runtime contract: Q12.20 values use Int32; widened products use Int64.

qShift : Int
qShift = 20

qOne : Int32
qOne = 1048576

abs32 : Int32 -> Int32
abs32 x = let m = shiftR x 31 in (xor x m) - m

qmul : Int32 -> Int32 -> Int32
qmul a b =
  let prod : Int64
      prod = (fromIntegral a) * (fromIntegral b)
  in fromIntegral (shiftR prod qShift)

qdivSafe : Int32 -> Int32 -> Int32
qdivSafe num den =
  if den <= 0
    then 0
    else
      let num64 : Int64
          num64 = shiftL (fromIntegral num) qShift
          den64 : Int64
          den64 = fromIntegral den
      in fromIntegral (quot num64 den64)

softsignQ20 : Int32 -> Int32
softsignQ20 x = qdivSafe x (qOne + abs32 x)

quantmoid4Q20 : Int32 -> Int32
quantmoid4Q20 x =
  let ax = abs32 x
      cl = if ax < qOne then ax else qOne
      v  = cl - qOne
      v64 : Int64
      v64 = fromIntegral v
      vv : Int32
      vv = fromIntegral (shiftR (v64 * v64) (qShift + 1))
  in if 0 < x then qOne - vv else vv

-- Strict tail-recursive fold (Csimma rule: avoid lazy thunk buildup in extracted Haskell)
foldlStrict : {a b : Set} -> (b -> a -> b) -> b -> List a -> b
foldlStrict f acc []       = acc
foldlStrict f acc (x ∷ xs) =
  let acc' = f acc x
  in seq acc' (foldlStrict f acc' xs)

sum32 : List Int32 -> Int32
sum32 = foldlStrict _+_ 0

max32List : Int32 -> List Int32 -> Int32
max32List = foldlStrict (\a b -> if b > a then b else a)

-- Permutation-Equivariant DeepSets (DS: Mean || Max Softsign) + Iterative-CHAD dW_ent
deepSetsStepChad : Int32 -> List Int32 -> Int32 -> Int32 × Int32
deepSetsStepChad w es dAgg =
  let n     = length es
      k     = if 0 < n then fromIntegral n else 1
      zs    = map (qmul w) es
      phis  = map softsignQ20 zs
      meanP = quot (sum32 phis) k
      maxP  = max32List (- qOne) phis
      agg   = shiftR meanP 1 + shiftR maxP 1
      dMean = quot (shiftR dAgg 1) k
      dPhi e phi z =
        let dMax = if phi == maxP then shiftR dAgg 1 else 0
            den  = qOne + abs32 z
        in qmul (qdivSafe (dMean + dMax) (qmul den den)) e
      dW    = sum32 (zipWith3 dPhi es phis zs)
  in (agg , dW)

-- State-Dependent GRU (Softsign state act, QuantMoid4 gate) + Iterative-CHAD (#1 Nash Anchor)
gruChadStep : Int32 -> Int32 -> Int32 -> Int32 -> Int32 -> Int32 -> Int32 × Int32 × Int32 × Int32
gruChadStep x h wRec uGate dH lr =
  let uIn  = x + qmul uGate h
      g    = quantmoid4Q20 uIn
      omg  = qOne - g
      hLin = qmul g x + qmul (qmul omg wRec) h
      hNxt = softsignQ20 hLin
      den  = qOne + abs32 hLin
      dLin = qdivSafe dH (qmul den den)
      axu  = abs32 uIn
      dgW  = if axu < qOne then qOne - axu else 0
      dG   = qmul (qmul dLin (x - qmul wRec h)) dgW
      dh0  = qmul dLin (qmul omg wRec) + qmul dG uGate
      dwR  = qmul dLin (qmul omg h)
      duG  = qmul dG h
      wNew = wRec  + qmul lr dwR - shiftR wRec  16
      uNew = uGate + qmul lr duG - shiftR uGate 16
  in (hNxt , dh0 , wNew , uNew)

{-# COMPILE AGDA2HS qShift #-}
{-# COMPILE AGDA2HS qOne #-}
{-# COMPILE AGDA2HS abs32 #-}
{-# COMPILE AGDA2HS qmul #-}
{-# COMPILE AGDA2HS qdivSafe #-}
{-# COMPILE AGDA2HS softsignQ20 #-}
{-# COMPILE AGDA2HS quantmoid4Q20 #-}
{-# COMPILE AGDA2HS foldlStrict #-}
{-# COMPILE AGDA2HS sum32 #-}
{-# COMPILE AGDA2HS max32List #-}
{-# COMPILE AGDA2HS deepSetsStepChad #-}
{-# COMPILE AGDA2HS gruChadStep #-}
