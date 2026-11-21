{-# OPTIONS
--erasure
--experimental-lazy-instances
--lossy-unification
--syntactic-equality=1
--no-eta-equality
--prop
--with-K
--no-fast-reduce
--no-projection-like
--erased-quotients
--erased-funext
--erased-propext
--auto-inline
--exact-split
--rewriting
--confluence-check
#-}

module FullCoupled.CanonicalLearnerMonolith where

------------------------------------------------------------------------
-- The small proof surface follows the relevant Agdalache patterns:
-- erased S0 witnesses, propositional equality, and relation support.
-- The learner has no C pointer, IORef, StablePtr, MVar, or CFuture API.
------------------------------------------------------------------------

-- Follow the standard Agda2HS base-library convention used in Viktor
-- Csimma's examples: Haskell.Prelude is the shared Agda/Haskell surface.
-- It re-exports equality, builtin Nat, products, and primitive proof types.
-- Vec's Nat index is erased, so no runtime length or Peano traversal remains.
open import Agda.Primitive using (Level; _⊔_)
open import Haskell.Prelude public
open import Agda.Builtin.Erased.Funext public
open import Agda.Builtin.Erased.Propext public
open import Agda.Builtin.Erased.Quotient public
open import Agda.Builtin.Equality.Rewrite public

------------------------------------------------------------------------
-- Erased proof packaging
------------------------------------------------------------------------

record S0 {i j : Level} (A : Set i) (@0 P : A → Set j) : Set (i ⊔ j) where
  no-eta-equality
  constructor packS0
  field
    valueS0 : A
    @0 proofS0 : P valueS0

open S0 public
{-# COMPILE AGDA2HS S0 newtype #-}

∃0 : ∀ {i j} {A : Set i} → @0 (A → Set j) → Set (i ⊔ j)
∃0 {A = A} P = S0 A P
{-# COMPILE AGDA2HS ∃0 #-}

------------------------------------------------------------------------
-- Equality and relation support
------------------------------------------------------------------------

@0 cong
  : ∀ {i} {A B : Set i} (f : A → B) {x y : A}
  → x ≡ y → f x ≡ f y
cong f refl = refl

@0 sym : ∀ {i} {A : Set i} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

@0 trans
  : ∀ {i} {A : Set i} {x y z : A}
  → x ≡ y → y ≡ z → x ≡ z
trans refl yz = yz

@0 subst
  : ∀ {i} {A : Set i} {x y : A}
  → (P : A → Set) → x ≡ y → P x → P y
subst P refl px = px

infix 4 _≢_
_≢_ : ∀ {i} {A : Set i} → A → A → Set i
x ≢ y = (x ≡ y) → ⊥

data _⊎_ {i j : Level} (A : Set i) (B : Set j) : Set (i ⊔ j) where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

------------------------------------------------------------------------
-- Erased-length vectors
------------------------------------------------------------------------

data Vec (A : Set) : (@0 n : Nat) → Set where
  VNil  : Vec A zero
  VCons : ∀ {@0 n} → A → Vec A n → Vec A (suc n)

{-# COMPILE AGDA2HS Vec #-}

mapVec : ∀ {A B : Set} {@0 n} → (A → B) → Vec A n → Vec B n
mapVec f VNil = VNil
mapVec f (VCons x xs) = VCons (f x) (mapVec f xs)
{-# COMPILE AGDA2HS mapVec #-}

zipWithVec
  : ∀ {A B C : Set} {@0 n}
  → (A → B → C) → Vec A n → Vec B n → Vec C n
zipWithVec f VNil VNil = VNil
zipWithVec f (VCons x xs) (VCons y ys) =
  VCons (f x y) (zipWithVec f xs ys)
{-# COMPILE AGDA2HS zipWithVec #-}

mapVec-id : ∀ {A : Set} {@0 n} (xs : Vec A n) → mapVec (λ x → x) xs ≡ xs
mapVec-id VNil = refl
mapVec-id (VCons x xs) rewrite mapVec-id xs = refl
{-# REWRITE mapVec-id #-}

------------------------------------------------------------------------
-- Q12.20 fixed-point representation
--
-- The Agda type is opaque. Its extracted representation is Data.Int.Int32.
-- Every arithmetic primitive widens to Int64, rounds ties to even, then
-- saturates to Int32. Division by zero is represented explicitly.
------------------------------------------------------------------------

{-# FOREIGN AGDA2HS
import Data.Int (Int8, Int32, Int64)
import Data.Word (Word32, Word64)
import qualified Data.Int
import qualified Data.Word
import qualified Data.Bits as Bits
import qualified Data.Vector.Unboxed as U

type Vec8 = U.Vector Int8
type Vec32 = U.Vector Int32
type Vec64 = U.Vector Int64

satInt32 :: Int64 -> Int32
satInt32 n
  | n < fromIntegral (minBound :: Int32) = minBound
  | n > fromIntegral (maxBound :: Int32) = maxBound
  | otherwise = fromIntegral n

roundDivEven :: Int64 -> Int64 -> Int64
roundDivEven n d =
  let (q, r) = quotRem n d
      twiceR = 2 * abs r
      absD = abs d
      step = signum n * signum d
  in case compare twiceR absD of
       LT -> q
       GT -> q + step
       EQ -> if even q then q else q + step

qOneRaw :: Int64
qOneRaw = 1048576

int32Zero :: Int32
int32Zero = 0

int32OneQ20 :: Int32
int32OneQ20 = 1048576

int32Sixteen :: Int32
int32Sixteen = 16

addInt32 :: Int32 -> Int32 -> Int32
addInt32 x y = satInt32 (fromIntegral x + fromIntegral y)

subInt32 :: Int32 -> Int32 -> Int32
subInt32 x y = satInt32 (fromIntegral x - fromIntegral y)

mulQ20Int32 :: Int32 -> Int32 -> Int32
mulQ20Int32 = qMulRaw

negInt32 :: Int32 -> Int32
negInt32 x = satInt32 (negate (fromIntegral x))

absInt32 :: Int32 -> Int32
absInt32 x = satInt32 (abs (fromIntegral x))

qMulRaw :: Int32 -> Int32 -> Int32
qMulRaw x y =
  satInt32 (roundDivEven (fromIntegral x * fromIntegral y) qOneRaw)

qDivRaw :: Int32 -> Int32 -> Int32
qDivRaw _ 0 = 0
qDivRaw x y =
  satInt32 (roundDivEven (fromIntegral x * qOneRaw) (fromIntegral y))

qSoftsignRaw :: Int32 -> Int32
qSoftsignRaw x =
  let n = fromIntegral x * qOneRaw
      d = qOneRaw + abs (fromIntegral x)
  in satInt32 (roundDivEven n d)

qShiftedGateRaw :: Int32 -> Int32
qShiftedGateRaw x =
  let wideX = 4 * fromIntegral x :: Int64
      numerator = wideX * qOneRaw
      denominator = qOneRaw + abs wideX
      soft = roundDivEven numerator denominator
  in satInt32 (roundDivEven (qOneRaw + soft) 2)

-- Stockfish Quantmoid4 integer forward, rescaled to Q12.20.
-- The C1 training shadow is a separate object and is not this discrete kernel.
qQuantmoid4Raw :: Int32 -> Int32
qQuantmoid4Raw x =
  let magnitude = min 127 (quot (abs (fromIntegral x) * 127) qOneRaw)
      v = magnitude - 127
      vv = quot (v * v) 256
      output = if x > 0 then 126 - vv else vv
  in satInt32 (roundDivEven (output * qOneRaw) 127)

qLinearRowsRaw :: Int32 -> Int32 -> Vec32 -> Vec32 -> Vec32 -> Vec32
qLinearRowsRaw rows cols weights bias input =
  let outN = max 0 (fromIntegral rows)
      inN = max 0 (fromIntegral cols)
      weightN = U.length weights
      inputN = U.length input
      dotRow row =
        let start = row * inN
            n = min inN (min inputN (max 0 (weightN - start)))
            acc = U.ifoldl' (\total i x ->
                    if i < n
                      then total + fromIntegral
                        (qMulRaw (U.unsafeIndex weights (start + i)) x)
                      else total)
                  (0 :: Int64) input
            b = if row < U.length bias then fromIntegral (U.unsafeIndex bias row) else 0
        in satInt32 (acc + b)
  in U.generate outN dotRow

-- Optional packed inference path: signed Q1.6 Int8 weights, Q12.20 inputs/outputs.
qLinearRowsInt8Raw :: Int32 -> Int32 -> Vec8 -> Vec32 -> Vec32 -> Vec32
qLinearRowsInt8Raw rows cols weights bias input =
  let outN = max 0 (fromIntegral rows)
      inN = max 0 (fromIntegral cols)
      weightN = U.length weights
      inputN = U.length input
      dotRow row =
        let start = row * inN
            n = min inN (min inputN (max 0 (weightN - start)))
            acc = U.ifoldl' (\total i x ->
                    if i < n
                      then
                        let w = fromIntegral (U.unsafeIndex weights (start + i)) * 16384
                        in total + fromIntegral (qMulRaw (satInt32 w) x)
                      else total)
                  (0 :: Int64) input
            b = if row < U.length bias then fromIntegral (U.unsafeIndex bias row) else 0
        in satInt32 (acc + b)
  in U.generate outN dotRow

qShiftedGateVecRaw :: Vec32 -> Vec32
qShiftedGateVecRaw = U.map qShiftedGateRaw

qSoftsignVecRaw :: Vec32 -> Vec32
qSoftsignVecRaw = U.map qSoftsignRaw

qQuantmoid4VecRaw :: Vec32 -> Vec32
qQuantmoid4VecRaw = U.map qQuantmoid4Raw

qConvexMixRaw :: Vec32 -> Vec32 -> Vec32 -> Vec32
qConvexMixRaw gate previous candidate =
  U.zipWith3 (\g old new ->
    let keep = qMulRaw g old
        useNew = qMulRaw (satInt32 (qOneRaw - fromIntegral g)) new
    in satInt32 (fromIntegral keep + fromIntegral useNew))
    gate previous candidate

qMadLayerNormRaw :: Vec32 -> Vec32
qMadLayerNormRaw xs
  | U.null xs = U.empty
  | otherwise =
      let n = fromIntegral (U.length xs) :: Int64
          sumX = U.foldl' (\a x -> a + fromIntegral x) 0 xs
          mean = satInt32 (roundDivEven sumX n)
          centered = U.map (\x -> satInt32 (fromIntegral x - fromIntegral mean)) xs
          madSum = U.foldl' (\a x -> a + abs (fromIntegral x)) 0 centered
          mad = roundDivEven madSum n
          epsilon = 256 :: Int64 -- Q12.20 epsilon = 2^-12
          denominator = max 1 (mad + epsilon)
      in U.map (\x ->
           satInt32 (roundDivEven (fromIntegral x * qOneRaw) denominator))
           centered

q4SoftmaxRaw :: Int32 -> Vec32 -> Vec32
q4SoftmaxRaw temperature logits
  | U.null logits = U.empty
  | otherwise =
      let t = max 1 temperature
          maximumLogit = U.maximum logits
          unnormalised = U.map (\z ->
            max 1 (qQuantmoid4Raw (qDivRaw (satInt32 (fromIntegral z - fromIntegral maximumLogit)) t)))
            logits
          total = U.foldl' (\acc x -> acc + fromIntegral x) (0 :: Int64) unnormalised
          n = U.length unnormalised
          prefixTotal = U.ifoldl' (\acc i x ->
            if i + 1 < n
              then acc + fromIntegral
                (satInt32 (roundDivEven (fromIntegral x * qOneRaw) total))
              else acc)
            (0 :: Int64) unnormalised
      in U.imap (\i x ->
           if i + 1 == n
             then satInt32 (qOneRaw - prefixTotal)
             else satInt32 (roundDivEven (fromIntegral x * qOneRaw) total))
           unnormalised

qPrefixMidpointsRaw :: Vec32 -> Vec32
qPrefixMidpointsRaw widths =
  U.generate (U.length widths) (\i ->
    let prefix = U.ifoldl' (\acc j x -> if j < i then acc + fromIntegral x else acc)
                   (0 :: Int64) widths
        width = fromIntegral (U.unsafeIndex widths i)
    in satInt32 (prefix + roundDivEven width 2))

qSlice32Raw :: Int32 -> Int32 -> Vec32 -> Vec32
qSlice32Raw start count xs =
  let s = max 0 (min (U.length xs) (fromIntegral start))
      n = max 0 (min (U.length xs - s) (fromIntegral count))
  in U.slice s n xs

qVecLengthRaw :: Vec32 -> Int32
qVecLengthRaw = fromIntegral . U.length

qAppend32Raw :: Vec32 -> Vec32 -> Vec32
qAppend32Raw = (U.++)

qZeroVec32Raw :: Int32 -> Vec32
qZeroVec32Raw n = U.replicate (max 0 (fromIntegral n)) 0

pcgAdvanceRaw :: Word64 -> Word64
pcgAdvanceRaw state = state * 6364136223846793005 + 1442695040888963407

pcgWord32Raw :: Word64 -> Word32
pcgWord32Raw state =
  let next = pcgAdvanceRaw state
      shifted = fromIntegral (Bits.shiftR (Bits.xor (Bits.shiftR next 18) next) 27)
      rotation = fromIntegral (Bits.shiftR next 59)
  in Bits.rotateR (shifted :: Word32) rotation

normalTableRaw :: Vec32
normalTableRaw = U.fromList [-1953204, -1382021, -1059062, -813589, -607174, -421841, -248721, -82194, 82194, 248721, 421841, 607174, 813589, 1059062, 1382021, 1953204]

gumbelTableRaw :: Vec32
gumbelTableRaw = U.fromList [-1303301, -903532, -648633, -438929, -249398, -68827, 109563, 290966, 480289, 683080, 906615, 1161749, 1466888, 1858654, 2430921, 3617486]

-- Sixteen-bin lognormal persistence quantiles (median 4, sigma 1/2),
-- precomputed offline from the quantized-normal table. No runtime exp/log.
durationTableRaw :: Vec32
durationTableRaw = U.fromList [2, 2, 2, 3, 3, 3, 4, 4, 4, 5, 5, 5, 6, 7, 8, 10]

qNormalNoiseVecRaw :: Word64 -> Int32 -> Vec32
qNormalNoiseVecRaw seed count =
  U.generate (max 0 (fromIntegral count)) (\i ->
    let word = pcgWord32Raw (seed + fromIntegral i * 1442695040888963407)
        index = fromIntegral (Bits..&. word 15)
    in U.unsafeIndex normalTableRaw index)

qNoiseDurationRaw :: Word64 -> Int32
qNoiseDurationRaw seed =
  let index = fromIntegral (Bits..&. (pcgWord32Raw seed) 15)
  in U.unsafeIndex durationTableRaw index

qSqrt64Raw :: Int64 -> Int64
qSqrt64Raw n
  | n <= 0 = 0
  | otherwise = go 0 2147483647
  where
    go lo hi
      | lo + 1 >= hi = lo
      | otherwise =
          let mid = lo + quot (hi - lo) 2
          in if mid * mid <= n then go mid hi else go lo mid

qFactorRaw :: Int32 -> Int32
qFactorRaw x
  | x == 0 = 0
  | otherwise =
      let root = qSqrt64Raw (abs (fromIntegral x) * qOneRaw)
          signed = if x < 0 then negate root else root
      in satInt32 signed

qFactorizedNoisyLinearRaw
  :: Int32 -> Int32 -> Vec32 -> Vec32 -> Vec32 -> Vec32
  -> Vec32 -> Vec32 -> Vec32 -> Vec32
qFactorizedNoisyLinearRaw rows cols muWeights sigmaWeights muBias sigmaBias input inputNoise outputNoise =
  let outN = max 0 (fromIntegral rows)
      inN = max 0 (fromIntegral cols)
      weightN = U.length muWeights
      inputN = U.length input
      inputFactors = U.map qFactorRaw inputNoise
      outputFactors = U.map qFactorRaw outputNoise
      noisyWeight row col =
        let ix = row * inN + col
            mu = if ix < weightN then U.unsafeIndex muWeights ix else 0
            sigma = if ix < U.length sigmaWeights then U.unsafeIndex sigmaWeights ix else 0
            ei = if col < U.length inputFactors then U.unsafeIndex inputFactors col else 0
            eo = if row < U.length outputFactors then U.unsafeIndex outputFactors row else 0
            noise = qMulRaw ei eo
        in satInt32 (fromIntegral mu + fromIntegral (qMulRaw sigma noise))
      noisyBias row =
        let mu = if row < U.length muBias then U.unsafeIndex muBias row else 0
            sigma = if row < U.length sigmaBias then U.unsafeIndex sigmaBias row else 0
            eo = if row < U.length outputFactors then U.unsafeIndex outputFactors row else 0
        in satInt32 (fromIntegral mu + fromIntegral (qMulRaw sigma eo))
      output row =
        let n = min inN (min inputN (max 0 (weightN - row * inN)))
            acc = U.ifoldl' (\total i x ->
                    if i < n
                      then total + fromIntegral (qMulRaw (noisyWeight row i) x)
                      else total)
                  (0 :: Int64) input
        in satInt32 (acc + fromIntegral (noisyBias row))
  in U.generate outN output

qGumbelMaxSelectRaw :: Word64 -> Int32 -> Vec32 -> Int32
qGumbelMaxSelectRaw seed temperature logits
  | U.null logits = 0
  | otherwise =
      let tau = max 1 temperature
          score i z =
            let state = seed + fromIntegral i * 1442695040888963407
                index = fromIntegral (Bits..&. (pcgWord32Raw state) 15)
                g = U.unsafeIndex gumbelTableRaw index
            in fromIntegral (qDivRaw z tau) + fromIntegral g :: Int64
          (_,bestIndex) = U.ifoldl' (\(best,bestI) i z ->
            let candidate = score i z
            in if candidate > best then (candidate,i) else (best,bestI))
            (minBound :: Int64,0) logits
      in fromIntegral bestIndex

qMunchausenLogTableRaw :: Vec32
qMunchausenLogTableRaw = U.fromList [-4360905, -3634087, -3208927, -2907270, -2673287, -2482109, -2320470, -2180452, -2056948, -1946470, -1846530, -1755292, -1671361, -1593653, -1521309, -1453635, -1390065, -1330131, -1273437, -1219652, -1168492, -1119712, -1073101, -1028474, -985669, -944543, -904970, -866835, -830039, -794491, -760108, -726817, -694551, -663248, -632852, -603313, -574583, -546619, -519382, -492835, -466942, -441674, -417001, -392895, -369330, -346284, -323733, -301657, -280036, -258852, -238087, -217726, -197752, -178152, -158912, -140018, -121458, -103222, -85297, -67674, -50341, -33291, -16513, 0]

qLogProbRaw :: Int32 -> Int32
qLogProbRaw probability =
  let p = max 16 (min 1048576 probability)
      scaled = roundDivEven (fromIntegral p * 64) qOneRaw
      index = max 1 (min 64 (fromIntegral scaled))
  in U.unsafeIndex qMunchausenLogTableRaw (index - 1)

qMunchausenRewardRaw :: Int32 -> Int32 -> Int32
qMunchausenRewardRaw reward probability =
  let alpha = 65536 :: Int32
      tau = 131072 :: Int32
      shaping = qMulRaw (qMulRaw alpha tau) (qLogProbRaw probability)
  in satInt32 (fromIntegral reward + fromIntegral shaping)

divQ20Int32 :: Int32 -> Int32 -> Div32Result
divQ20Int32 _ 0 = Div32ByZero
divQ20Int32 x y =
  Div32Quotient
    (satInt32 (roundDivEven (fromIntegral x * qOneRaw) (fromIntegral y)))

qSarsa3TargetRaw
  :: Int32 -> Int32 -> Int32 -> Int32 -> Int32 -> Int32 -> Vec32 -> Vec32
qSarsa3TargetRaw reward0 reward1 reward2 terminal0 terminal1 terminal2 bootstrap =
  let gamma = 1038090 :: Int32
      gamma2 = qMulRaw gamma gamma
      gamma3 = qMulRaw gamma2 gamma
      r0 = fromIntegral reward0 :: Int64
      r01 = r0 + fromIntegral (qMulRaw gamma reward1)
      r012 = r01 + fromIntegral (qMulRaw gamma2 reward2)
      base
        | terminal0 /= 0 = r0
        | terminal1 /= 0 = r01
        | otherwise = r012
      boot = if terminal0 /= 0 || terminal1 /= 0 || terminal2 /= 0 then 0 else gamma3
  in U.map (\q -> satInt32 (base + fromIntegral (qMulRaw boot q))) bootstrap

qAddL2GradientRaw :: Vec32 -> Vec32 -> Vec32
-- Input is an update direction, so L2 decay points toward zero.
qAddL2GradientRaw gradient weights =
  U.zipWith (\g w ->
    satInt32 (fromIntegral g - fromIntegral (qMulRaw 16 w)))
    gradient weights

qAddVec32Raw :: Vec32 -> Vec32 -> Vec32
qAddVec32Raw = U.zipWith addInt32

qNegVec32Raw :: Vec32 -> Vec32
qNegVec32Raw = U.map negInt32

qScaleVec32Raw :: Int32 -> Vec32 -> Vec32
qScaleVec32Raw scalar = U.map (qMulRaw scalar)

qTraceAdvanceRaw :: Int32 -> Vec32 -> Vec32 -> Vec32
qTraceAdvanceRaw decay previous gradient =
  U.generate (max (U.length previous) (U.length gradient)) (\i ->
    let old = if i < U.length previous then U.unsafeIndex previous i else 0
        new = if i < U.length gradient then U.unsafeIndex gradient i else 0
    in addInt32 (qMulRaw decay old) new)

qLogProbabilityCotangentRaw :: Int32 -> Vec32 -> Vec32
qLogProbabilityCotangentRaw action probabilities =
  U.imap (\i p ->
    if i == max 0 (fromIntegral action)
      then qDivRaw (fromIntegral qOneRaw) p
      else 0) probabilities

qEmbedActionCotangentRaw :: Int32 -> Int32 -> Int32 -> Vec32 -> Vec32
qEmbedActionCotangentRaw action quantiles actions cotangent =
  let start = max 0 (fromIntegral action) * max 0 (fromIntegral quantiles)
      total = max 0 (fromIntegral actions) * max 0 (fromIntegral quantiles)
  in U.generate total (\i ->
       if i >= start && i < start + U.length cotangent
         then U.unsafeIndex cotangent (i - start)
         else 0)

qLinearRowsVJPRaw
  :: Int32 -> Int32 -> Vec32 -> Vec32 -> Vec32 -> Vec32 -> Vec32
qLinearRowsVJPRaw rows cols weights bias input outputCotangent =
  let outN = max 0 (fromIntegral rows)
      inN = max 0 (fromIntegral cols)
      gradWeights = U.generate (outN * inN) (\ix ->
        let row = if inN == 0 then 0 else quot ix inN
            col = if inN == 0 then 0 else rem ix inN
            dy = if row < U.length outputCotangent then U.unsafeIndex outputCotangent row else 0
            x = if col < U.length input then U.unsafeIndex input col else 0
        in qMulRaw dy x)
      gradBias = U.generate outN (\row ->
        if row < U.length outputCotangent then U.unsafeIndex outputCotangent row else 0)
      gradInput = U.generate inN (\col ->
        let total = U.ifoldl' (\acc row dy ->
              let ix = row * inN + col
                  w = if ix < U.length weights then U.unsafeIndex weights ix else 0
              in acc + fromIntegral (qMulRaw w dy))
              (0 :: Int64) outputCotangent
        in satInt32 total)
  in qAppend32Raw gradWeights (qAppend32Raw gradBias gradInput)

qFactorizedNoisyLinearVJPRaw
  :: Int32 -> Int32 -> Vec32 -> Vec32 -> Vec32 -> Vec32
  -> Vec32 -> Vec32 -> Vec32 -> Vec32
  -> Vec32
qFactorizedNoisyLinearVJPRaw rows cols muWeights sigmaWeights muBias sigmaBias
    input inputNoise outputNoise outputCotangent =
  let outN = max 0 (fromIntegral rows)
      inN = max 0 (fromIntegral cols)
      gradMuWeights = U.generate (outN * inN) (\ix ->
        let row = if inN == 0 then 0 else quot ix inN
            col = if inN == 0 then 0 else rem ix inN
            dy = if row < U.length outputCotangent then U.unsafeIndex outputCotangent row else 0
            x = if col < U.length input then U.unsafeIndex input col else 0
        in qMulRaw dy x)
      gradSigmaWeights = U.generate (outN * inN) (\ix ->
        let row = if inN == 0 then 0 else quot ix inN
            col = if inN == 0 then 0 else rem ix inN
            dy = if row < U.length outputCotangent then U.unsafeIndex outputCotangent row else 0
            x = if col < U.length input then U.unsafeIndex input col else 0
            ei = if col < U.length inputNoise then qFactorRaw (U.unsafeIndex inputNoise col) else 0
            eo = if row < U.length outputNoise then qFactorRaw (U.unsafeIndex outputNoise row) else 0
        in qMulRaw (qMulRaw dy (qMulRaw ei eo)) x)
      gradMuBias = U.generate outN (\row ->
        if row < U.length outputCotangent then U.unsafeIndex outputCotangent row else 0)
      gradSigmaBias = U.generate outN (\row ->
        let dy = if row < U.length outputCotangent then U.unsafeIndex outputCotangent row else 0
            eo = if row < U.length outputNoise then qFactorRaw (U.unsafeIndex outputNoise row) else 0
        in qMulRaw dy eo)
      gradInput = U.generate inN (\col ->
        let total = U.ifoldl' (\acc row dy ->
              let ix = row * inN + col
                  mu = if ix < U.length muWeights then U.unsafeIndex muWeights ix else 0
                  sigma = if ix < U.length sigmaWeights then U.unsafeIndex sigmaWeights ix else 0
                  ei = if col < U.length inputNoise then qFactorRaw (U.unsafeIndex inputNoise col) else 0
                  eo = if row < U.length outputNoise then qFactorRaw (U.unsafeIndex outputNoise row) else 0
                  noisy = addInt32 mu (qMulRaw sigma (qMulRaw ei eo))
              in acc + fromIntegral (qMulRaw noisy dy))
              (0 :: Int64) outputCotangent
        in satInt32 total)
  in qAppend32Raw gradMuWeights
       (qAppend32Raw gradSigmaWeights
         (qAppend32Raw gradMuBias
           (qAppend32Raw gradSigmaBias gradInput)))

qSoftsignVJPRaw :: Vec32 -> Vec32 -> Vec32
qSoftsignVJPRaw preactivation outputCotangent =
  U.zipWith (\x dy ->
    let denominator = satInt32 (qOneRaw + abs (fromIntegral x))
        inverse = qDivRaw (fromIntegral qOneRaw) denominator
        derivative = qMulRaw inverse inverse
    in qMulRaw dy derivative)
    preactivation outputCotangent

qShiftedGateVJPRaw :: Vec32 -> Vec32 -> Vec32
qShiftedGateVJPRaw preactivation outputCotangent =
  U.zipWith (\x dy ->
    let denominator = satInt32 (qOneRaw + 4 * abs (fromIntegral x))
        inverse = qDivRaw (fromIntegral qOneRaw) denominator
        derivative = qMulRaw 2097152 (qMulRaw inverse inverse)
    in qMulRaw dy derivative)
    preactivation outputCotangent

qConvexMixVJPRaw :: Vec32 -> Vec32 -> Vec32 -> Vec32 -> Vec32
qConvexMixVJPRaw gate previous candidate outputCotangent =
  let n = minimum [U.length gate, U.length previous, U.length candidate, U.length outputCotangent]
      gateCot = U.generate n (\i ->
        let g = U.unsafeIndex gate i
            old = U.unsafeIndex previous i
            new = U.unsafeIndex candidate i
            dy = U.unsafeIndex outputCotangent i
        in qMulRaw dy (subInt32 old new))
      previousCot = U.generate n (\i ->
        qMulRaw (U.unsafeIndex outputCotangent i) (U.unsafeIndex gate i))
      candidateCot = U.generate n (\i ->
        let g = U.unsafeIndex gate i
        in qMulRaw (U.unsafeIndex outputCotangent i) (subInt32 (fromIntegral qOneRaw) g))
  in qAppend32Raw gateCot (qAppend32Raw previousCot candidateCot)

qMadLayerNormVJPRaw :: Vec32 -> Vec32 -> Vec32
qMadLayerNormVJPRaw values outputCotangent
  | U.null values || U.null outputCotangent = U.replicate (U.length values) 0
  | otherwise =
      let n = fromIntegral (U.length values) :: Int64
          sumX = U.foldl' (\acc x -> acc + fromIntegral x) 0 values
          mean = satInt32 (roundDivEven sumX n)
          centered = U.map (\x -> subInt32 x mean) values
          madSum = U.foldl' (\acc x -> acc + abs (fromIntegral x)) 0 centered
          mad = satInt32 (roundDivEven madSum n)
          denominator = satInt32 (fromIntegral mad + 256)
          dot = U.ifoldl' (\acc i c ->
                   let dy = if i < U.length outputCotangent then U.unsafeIndex outputCotangent i else 0
                   in acc + fromIntegral (qMulRaw dy c))
                 (0 :: Int64) centered
          averageDot = satInt32 (roundDivEven dot n)
          correction = qDivRaw (qDivRaw averageDot denominator) denominator
          uncentered = U.imap (\i c ->
            let dy = if i < U.length outputCotangent then U.unsafeIndex outputCotangent i else 0
                direct = qDivRaw dy denominator
                signedCorrection
                  | c > 0 = correction
                  | c < 0 = negInt32 correction
                  | otherwise = 0
            in subInt32 direct signedCorrection) centered
          meanCot = satInt32 (roundDivEven
            (U.foldl' (\acc x -> acc + fromIntegral x) 0 uncentered) n)
      in U.map (\x -> subInt32 x meanCot) uncentered

qQuantmoid4DerivativeRaw :: Int32 -> Int32
qQuantmoid4DerivativeRaw x
  | abs (fromIntegral x) >= qOneRaw = 0
  | otherwise = qMulRaw 1040384 (subInt32 (fromIntegral qOneRaw) (absInt32 x))

q4SoftmaxVJPRaw :: Int32 -> Vec32 -> Vec32 -> Vec32 -> Vec32
q4SoftmaxVJPRaw temperature logits probabilities probabilityCotangent
  | U.null logits = U.empty
  | otherwise =
      let t = max 1 temperature
          maximumLogit = U.maximum logits
          scaled = U.map (\z ->
            qDivRaw (subInt32 z maximumLogit) t) logits
          unnormalised = U.map qQuantmoid4Raw scaled
          total = U.foldl' (\acc q -> acc + fromIntegral q) (0 :: Int64) unnormalised
          expected = U.ifoldl' (\acc i p ->
            let dp = if i < U.length probabilityCotangent then U.unsafeIndex probabilityCotangent i else 0
            in acc + fromIntegral (qMulRaw p dp))
            (0 :: Int64) probabilities
          centeredCot = U.imap (\i dp ->
            let expectedQ20 = satInt32 expected
                q = U.unsafeIndex unnormalised i
                qPrime = qQuantmoid4DerivativeRaw (U.unsafeIndex scaled i)
                normalizedCot = qDivRaw (subInt32 dp expectedQ20) (satInt32 total)
            in qDivRaw (qMulRaw qPrime normalizedCot) t)
            probabilities
          maxIndex = U.maxIndex logits
          correction = U.foldl' (\acc x -> acc + fromIntegral x) (0 :: Int64) centeredCot
      in U.imap (\i x ->
           if i == maxIndex then subInt32 x (satInt32 correction) else x)
           centeredCot

qQuantileHuberLossRaw :: Int32 -> Vec32 -> Vec32 -> Vec32 -> Int32
qQuantileHuberLossRaw kappa midpoints targets predictions
  | n == 0 = 0
  | otherwise =
      let k = max 1 (fromIntegral kappa) :: Int64
          huberOverKappa delta =
            let d = abs (fromIntegral delta) :: Int64
                huber = if d <= k
                  then roundDivEven (d * d) (2 * qOneRaw)
                  else roundDivEven (k * (d - roundDivEven k 2)) qOneRaw
            in satInt32 (roundDivEven (huber * qOneRaw) k)
          total = U.ifoldl' (\acc j prediction ->
            let tau = fromIntegral (U.unsafeIndex midpoints j)
                inner = U.ifoldl' (\subtotal i target ->
                  let delta = subInt32 target prediction
                      weight = if delta < 0 then subInt32 (fromIntegral qOneRaw) (satInt32 tau) else satInt32 tau
                      term = qMulRaw weight (huberOverKappa delta)
                  in subtotal + fromIntegral term)
                  (0 :: Int64) targets
            in acc + inner)
            (0 :: Int64) predictions
      in satInt32 (roundDivEven total (fromIntegral n))
  where
    n = minimum [U.length midpoints, U.length targets, U.length predictions]

qQuantileHuberDirectionRaw :: Int32 -> Vec32 -> Vec32 -> Vec32 -> Vec32
qQuantileHuberDirectionRaw kappa midpoints targets predictions =
  let n = minimum [U.length midpoints, U.length targets, U.length predictions]
      k = max 1 kappa
  in U.generate n (\j ->
       let tau = U.unsafeIndex midpoints j
           total = U.ifoldl' (\acc _ target ->
             let delta = subInt32 target (U.unsafeIndex predictions j)
                 clipped = max (negInt32 k) (min k delta)
                 weight = if delta < 0
                   then subInt32 (fromIntegral qOneRaw) tau
                   else tau
             in acc + fromIntegral (qMulRaw weight (qDivRaw clipped k)))
             (0 :: Int64) targets
       in satInt32 (roundDivEven total (fromIntegral (max 1 n))))

qFQFBoundaryGradientRaw :: Vec32 -> Vec32 -> Vec32 -> Vec32
qFQFBoundaryGradientRaw widths midpoints values =
  let n = minimum [U.length widths, U.length midpoints, U.length values]
      boundary i = satInt32 (U.ifoldl' (\acc j width ->
                    if j < i then acc + fromIntegral width else acc)
                    (0 :: Int64) widths)
  in U.generate n (\i ->
       if i == 0 || i + 1 >= n
         then 0
         else
           let leftMid = U.unsafeIndex midpoints (i - 1)
               rightMid = U.unsafeIndex midpoints i
               leftValue = U.unsafeIndex values (i - 1)
               rightValue = U.unsafeIndex values i
               gap = subInt32 rightMid leftMid
               position = qDivRaw (subInt32 (boundary i) leftMid) gap
               atBoundary = addInt32 leftValue
                 (qMulRaw position (subInt32 rightValue leftValue))
           in subInt32 (qMulRaw 2097152 atBoundary)
                (addInt32 leftValue rightValue))

qFQFWidthCotangentRaw :: Vec32 -> Vec32
qFQFWidthCotangentRaw boundaryCotangent =
  U.generate (U.length boundaryCotangent) (\j ->
    let total = U.ifoldl' (\acc i x ->
          if i > j then acc + fromIntegral x else acc)
          (0 :: Int64) boundaryCotangent
    in satInt32 total)

qFQFFractionLogitDirectionRaw
  :: Vec32 -> Vec32 -> Vec32 -> Vec32 -> Vec32
qFQFFractionLogitDirectionRaw logits widths midpoints values =
  let boundaryCotangent = qFQFBoundaryGradientRaw widths midpoints values
      widthCotangent = qFQFWidthCotangentRaw boundaryCotangent
  in qNegVec32Raw (q4SoftmaxVJPRaw 1048576 logits widths widthCotangent)

qVecMeanRaw :: Vec32 -> Int32
qVecMeanRaw xs
  | U.null xs = 0
  | otherwise =
      satInt32 (roundDivEven
        (U.foldl' (\acc x -> acc + fromIntegral x) 0 xs)
        (fromIntegral (U.length xs)))

qObgdEffectiveStepRaw :: Int32 -> Int32 -> Int32 -> Vec32 -> Int32
qObgdEffectiveStepRaw alpha kappa delta trace =
  let l1 = U.foldl' (\acc x -> acc + abs (fromIntegral x)) (0 :: Int64) trace
      deltaBar = max qOneRaw (abs (fromIntegral delta))
      inverse x = satInt32 (quot (qOneRaw * qOneRaw) (max 1 x))
      multiplyDown x y =
        satInt32 (quot (fromIntegral x * fromIntegral y) qOneRaw)
      inverseKappa = inverse (fromIntegral (max 1 kappa))
      inverseDelta = inverse deltaBar
      inverseTrace = inverse l1
      safeStep = multiplyDown (multiplyDown inverseKappa inverseDelta) inverseTrace
  in if l1 == 0 then max 0 alpha else max 0 (min alpha safeStep)

qObgdUpdateRaw :: Int32 -> Int32 -> Int32 -> Vec32 -> Vec32 -> (Vec32, Int32)
qObgdUpdateRaw alpha kappa delta weights trace =
  let effectiveAlpha = qObgdEffectiveStepRaw alpha kappa delta trace
      scaledError = qMulRaw effectiveAlpha delta
      updated = U.zipWith (\w z -> addInt32 w (qMulRaw scaledError z)) weights trace
  in (updated, effectiveAlpha)

fqfMeanQ20 :: Vec32 -> Vec32 -> Int32
fqfMeanQ20 widths values
  | U.null values = 0
  | otherwise =
      let n = min (U.length widths) (U.length values)
          total = U.ifoldl' (\acc i w ->
            if i < n then acc + fromIntegral (qMulRaw w (U.unsafeIndex values i))
                     else acc) (0 :: Int64) widths
      in satInt32 (roundDivEven total qOneRaw)

qIndex32 :: Vec32 -> Int32 -> Int32
qIndex32 xs i
  | U.null xs = 0
  | otherwise = U.unsafeIndex xs (max 0 (min (U.length xs - 1) (fromIntegral i)))

int32GreaterThanOne :: Int32 -> Bool
int32GreaterThanOne x = x > 1

int32Decrement :: Int32 -> Int32
int32Decrement x = max 0 (x - 1)

-- Agda postulates below are backed by these Haskell-side implementations.
qLinearRowsQ20 = qLinearRowsRaw
qLinearRowsI8Q20 = qLinearRowsInt8Raw
qShiftedGateVec = qShiftedGateVecRaw
qSoftsignVec = qSoftsignVecRaw
qQuantmoid4Vec = qQuantmoid4VecRaw
qConvexMix = qConvexMixRaw
qMadLayerNorm = qMadLayerNormRaw
q4Softmax = q4SoftmaxRaw
qPrefixMidpoints = qPrefixMidpointsRaw
qSlice32 = qSlice32Raw
qVecLength = qVecLengthRaw
qAppend32 = qAppend32Raw
qZeroVec32 = qZeroVec32Raw
qNormalNoiseVec = qNormalNoiseVecRaw
qNoiseDuration = qNoiseDurationRaw
qWord64Next = pcgAdvanceRaw
qFactorizedNoisyLinear = qFactorizedNoisyLinearRaw
qGumbelMaxSelect = qGumbelMaxSelectRaw
qMunchausenReward = qMunchausenRewardRaw
qSarsa3Target = qSarsa3TargetRaw
qAddL2Gradient = qAddL2GradientRaw
qAddVec32 = qAddVec32Raw
qNegVec32 = qNegVec32Raw
qScaleVec32 = qScaleVec32Raw
qTraceAdvance = qTraceAdvanceRaw
qLogProbabilityCotangent = qLogProbabilityCotangentRaw
qEmbedActionCotangent = qEmbedActionCotangentRaw
qLinearRowsVJP = qLinearRowsVJPRaw
qFactorizedNoisyLinearVJP = qFactorizedNoisyLinearVJPRaw
qSoftsignVJP = qSoftsignVJPRaw
qShiftedGateVJP = qShiftedGateVJPRaw
qConvexMixVJP = qConvexMixVJPRaw
qMadLayerNormVJP = qMadLayerNormVJPRaw
q4SoftmaxVJP = q4SoftmaxVJPRaw
qQuantileHuberLoss = qQuantileHuberLossRaw
qQuantileHuberDirection = qQuantileHuberDirectionRaw
qFQFFractionLogitDirection = qFQFFractionLogitDirectionRaw
qVecMean = qVecMeanRaw
qObgdEffectiveStep = qObgdEffectiveStepRaw
qObgdUpdate = qObgdUpdateRaw
#-}

-- Fixed-width machine integers have no native Agda builtin counterpart.
-- Declare opaque Agda types and map them explicitly to Haskell's Data.Int and
-- Data.Word representations through Agda2HS. Int8 is only the optional packed
-- Stockfish-style inference-weight path; Q12.20 masters use Int32.
postulate
  Int32 Int64 Word32 Word64 Int8 : Set
  int32Sixteen : Int32
  Vec32 Vec64 Vec8 : Set
  int32Zero : Int32
  int32OneQ20 : Int32
  addInt32 : Int32 → Int32 → Int32
  subInt32 : Int32 → Int32 → Int32
  mulQ20Int32 : Int32 → Int32 → Int32
  negInt32 : Int32 → Int32
  absInt32 : Int32 → Int32

{-# COMPILE AGDA2HS int32Zero #-}
{-# COMPILE AGDA2HS int32OneQ20 #-}
{-# COMPILE AGDA2HS addInt32 #-}
{-# COMPILE AGDA2HS subInt32 #-}
{-# COMPILE AGDA2HS mulQ20Int32 #-}
{-# COMPILE AGDA2HS negInt32 #-}
{-# COMPILE AGDA2HS absInt32 #-}
{-# COMPILE AGDA2HS int32Sixteen #-}

{-# COMPILE AGDA2HS Int32 existing #-}
{-# COMPILE AGDA2HS Int64 existing #-}
{-# COMPILE AGDA2HS Word32 existing #-}
{-# COMPILE AGDA2HS Word64 existing #-}
{-# COMPILE AGDA2HS Int8 existing #-}
{-# COMPILE AGDA2HS Vec32 existing #-}
{-# COMPILE AGDA2HS Vec64 existing #-}
{-# COMPILE AGDA2HS Vec8 existing #-}

data Div32Result : Set where
  Div32ByZero : Div32Result
  Div32Quotient : Int32 → Div32Result

{-# COMPILE AGDA2HS Div32Result #-}

postulate
  divQ20Int32 : Int32 → Int32 → Div32Result

{-# COMPILE AGDA2HS divQ20Int32 #-}

record Q20 : Set where
  constructor MkQ20
  field
    rawQ20 : Int32

open Q20 public
{-# COMPILE AGDA2HS Q20 newtype #-}

data Q20DivResult : Set where
  Q20DivByZero : Q20DivResult
  Q20DivValue : Q20 → Q20DivResult

{-# COMPILE AGDA2HS Q20DivResult #-}

q20Zero : Q20
q20Zero = MkQ20 int32Zero
{-# COMPILE AGDA2HS q20Zero #-}

q20One : Q20
q20One = MkQ20 int32OneQ20
{-# COMPILE AGDA2HS q20One #-}

q20Add : Q20 → Q20 → Q20
q20Add (MkQ20 x) (MkQ20 y) = MkQ20 (addInt32 x y)
{-# COMPILE AGDA2HS q20Add #-}

q20Sub : Q20 → Q20 → Q20
q20Sub (MkQ20 x) (MkQ20 y) = MkQ20 (subInt32 x y)
{-# COMPILE AGDA2HS q20Sub #-}

q20Mul : Q20 → Q20 → Q20
q20Mul (MkQ20 x) (MkQ20 y) = MkQ20 (mulQ20Int32 x y)
{-# COMPILE AGDA2HS q20Mul #-}

q20Neg : Q20 → Q20
q20Neg (MkQ20 x) = MkQ20 (negInt32 x)
{-# COMPILE AGDA2HS q20Neg #-}

q20Abs : Q20 → Q20
q20Abs (MkQ20 x) = MkQ20 (absInt32 x)
{-# COMPILE AGDA2HS q20Abs #-}

q20Div : Q20 → Q20 → Q20DivResult
q20Div (MkQ20 x) (MkQ20 y) with divQ20Int32 x y
... | Div32ByZero = Q20DivByZero
... | Div32Quotient z = Q20DivValue (MkQ20 z)
{-# COMPILE AGDA2HS q20Div #-}

Q20Pair : Set
Q20Pair = Q20 × Q20
{-# COMPILE AGDA2HS Q20Pair #-}


------------------------------------------------------------------------
-- Typed integer vector FFI boundary
------------------------------------------------------------------------

postulate
  qLinearRowsQ20 : Int32 → Int32 → Vec32 → Vec32 → Vec32 → Vec32
  qLinearRowsI8Q20 : Int32 → Int32 → Vec8 → Vec32 → Vec32 → Vec32
  qShiftedGateVec : Vec32 → Vec32
  qSoftsignVec : Vec32 → Vec32
  qQuantmoid4Vec : Vec32 → Vec32
  qConvexMix : Vec32 → Vec32 → Vec32 → Vec32
  qMadLayerNorm : Vec32 → Vec32
  q4Softmax : Int32 → Vec32 → Vec32
  qPrefixMidpoints : Vec32 → Vec32
  qSlice32 : Int32 → Int32 → Vec32 → Vec32
  qVecLength : Vec32 → Int32
  qAppend32 : Vec32 → Vec32 → Vec32
  qZeroVec32 : Int32 → Vec32
  qNormalNoiseVec : Word64 → Int32 → Vec32
  qNoiseDuration : Word64 → Int32
  qWord64Next : Word64 → Word64
  qFactorizedNoisyLinear
    : Int32 → Int32 → Vec32 → Vec32 → Vec32 → Vec32
    → Vec32 → Vec32 → Vec32 → Vec32
  qGumbelMaxSelect : Word64 → Int32 → Vec32 → Int32
  qMunchausenReward : Int32 → Int32 → Int32
  qSarsa3Target : Int32 → Int32 → Int32 → Int32 → Int32 → Int32 → Vec32 → Vec32
  qAddL2Gradient : Vec32 → Vec32 → Vec32
  qAddVec32 : Vec32 → Vec32 → Vec32
  qNegVec32 : Vec32 → Vec32
  qScaleVec32 : Int32 → Vec32 → Vec32
  qTraceAdvance : Int32 → Vec32 → Vec32 → Vec32
  qLogProbabilityCotangent : Int32 → Vec32 → Vec32
  qEmbedActionCotangent : Int32 → Int32 → Int32 → Vec32 → Vec32
  qLinearRowsVJP : Int32 → Int32 → Vec32 → Vec32 → Vec32 → Vec32 → Vec32
  qFactorizedNoisyLinearVJP
    : Int32 → Int32 → Vec32 → Vec32 → Vec32 → Vec32
    → Vec32 → Vec32 → Vec32 → Vec32 → Vec32
  qSoftsignVJP : Vec32 → Vec32 → Vec32
  qShiftedGateVJP : Vec32 → Vec32 → Vec32
  qConvexMixVJP : Vec32 → Vec32 → Vec32 → Vec32 → Vec32
  qMadLayerNormVJP : Vec32 → Vec32 → Vec32
  q4SoftmaxVJP : Int32 → Vec32 → Vec32 → Vec32 → Vec32
  qQuantileHuberLoss : Int32 → Vec32 → Vec32 → Vec32 → Int32
  qQuantileHuberDirection : Int32 → Vec32 → Vec32 → Vec32 → Vec32
  qFQFFractionLogitDirection : Vec32 → Vec32 → Vec32 → Vec32 → Vec32
  qVecMean : Vec32 → Int32
  qObgdEffectiveStep : Int32 → Int32 → Int32 → Vec32 → Int32
  qObgdUpdate : Int32 → Int32 → Int32 → Vec32 → Vec32 → Vec32 × Int32
  fqfMeanQ20 : Vec32 → Vec32 → Int32
  qIndex32 : Vec32 → Int32 → Int32
  int32GreaterThanOne : Int32 → Bool
  int32Decrement : Int32 → Int32

{-# COMPILE AGDA2HS qLinearRowsQ20 #-}
{-# COMPILE AGDA2HS qLinearRowsI8Q20 #-}
{-# COMPILE AGDA2HS qShiftedGateVec #-}
{-# COMPILE AGDA2HS qSoftsignVec #-}
{-# COMPILE AGDA2HS qQuantmoid4Vec #-}
{-# COMPILE AGDA2HS qConvexMix #-}
{-# COMPILE AGDA2HS qMadLayerNorm #-}
{-# COMPILE AGDA2HS q4Softmax #-}
{-# COMPILE AGDA2HS qPrefixMidpoints #-}
{-# COMPILE AGDA2HS qSlice32 #-}
{-# COMPILE AGDA2HS qVecLength #-}
{-# COMPILE AGDA2HS qAppend32 #-}
{-# COMPILE AGDA2HS qZeroVec32 #-}
{-# COMPILE AGDA2HS qNormalNoiseVec #-}
{-# COMPILE AGDA2HS qNoiseDuration #-}
{-# COMPILE AGDA2HS qWord64Next #-}
{-# COMPILE AGDA2HS qFactorizedNoisyLinear #-}
{-# COMPILE AGDA2HS qGumbelMaxSelect #-}
{-# COMPILE AGDA2HS qMunchausenReward #-}
{-# COMPILE AGDA2HS qSarsa3Target #-}
{-# COMPILE AGDA2HS qAddL2Gradient #-}
{-# COMPILE AGDA2HS qAddVec32 #-}
{-# COMPILE AGDA2HS qNegVec32 #-}
{-# COMPILE AGDA2HS qScaleVec32 #-}
{-# COMPILE AGDA2HS qTraceAdvance #-}
{-# COMPILE AGDA2HS qLogProbabilityCotangent #-}
{-# COMPILE AGDA2HS qEmbedActionCotangent #-}
{-# COMPILE AGDA2HS qLinearRowsVJP #-}
{-# COMPILE AGDA2HS qFactorizedNoisyLinearVJP #-}
{-# COMPILE AGDA2HS qSoftsignVJP #-}
{-# COMPILE AGDA2HS qShiftedGateVJP #-}
{-# COMPILE AGDA2HS qConvexMixVJP #-}
{-# COMPILE AGDA2HS qMadLayerNormVJP #-}
{-# COMPILE AGDA2HS q4SoftmaxVJP #-}
{-# COMPILE AGDA2HS qQuantileHuberLoss #-}
{-# COMPILE AGDA2HS qQuantileHuberDirection #-}
{-# COMPILE AGDA2HS qFQFFractionLogitDirection #-}
{-# COMPILE AGDA2HS qVecMean #-}
{-# COMPILE AGDA2HS qObgdEffectiveStep #-}
{-# COMPILE AGDA2HS qObgdUpdate #-}
{-# COMPILE AGDA2HS fqfMeanQ20 #-}
{-# COMPILE AGDA2HS qIndex32 #-}
{-# COMPILE AGDA2HS int32GreaterThanOne #-}
{-# COMPILE AGDA2HS int32Decrement #-}

------------------------------------------------------------------------
-- State-independent affine-identity GRU
------------------------------------------------------------------------

record GRUParams : Set where
  constructor mkGRUParams
  field
    gruInputDim : Int32
    gruHiddenDim : Int32
    gruGateWeights : Vec32
    gruGateBias : Vec32
    gruCandidateWeights : Vec32
    gruCandidateBias : Vec32

open GRUParams public
{-# COMPILE AGDA2HS GRUParams #-}

gruStep : GRUParams → Vec32 → Vec32 → Vec32
gruStep p input previous =
  let gatePre = qLinearRowsQ20
        (gruHiddenDim p) (gruInputDim p)
        (gruGateWeights p) (gruGateBias p) input
      gate = qShiftedGateVec gatePre
      -- Candidate depends only on current input, never on previous hidden state.
      candidate = qLinearRowsQ20
        (gruHiddenDim p) (gruInputDim p)
        (gruCandidateWeights p) (gruCandidateBias p) input
      mixed = qConvexMix gate previous candidate
  in qSoftsignVec (qMadLayerNorm mixed)
{-# COMPILE AGDA2HS gruStep #-}

------------------------------------------------------------------------
-- Deterministic 16-quantile FQF critic
------------------------------------------------------------------------

record FQFParams : Set where
  constructor mkFQFParams
  field
    fqfFeatureDim : Int32
    fqfActionCount : Int32
    fqfFractionWeights : Vec32
    fqfFractionBias : Vec32
    fqfQuantileWeights : Vec32
    fqfQuantileBias : Vec32

open FQFParams public
{-# COMPILE AGDA2HS FQFParams #-}

record FQFOutput : Set where
  constructor mkFQFOutput
  field
    fqfWidths : Vec32
    fqfMidpoints : Vec32
    fqfValues : Vec32

open FQFOutput public
{-# COMPILE AGDA2HS FQFOutput #-}

fqfForward : FQFParams → Vec32 → Int32 → FQFOutput
fqfForward p features action =
  let n = int32Sixteen
      logits = qLinearRowsQ20 n (fqfFeatureDim p)
        (fqfFractionWeights p) (fqfFractionBias p) features
      widths = q4Softmax 1048576 logits
      midpoints = qPrefixMidpoints widths
      allValues = qLinearRowsQ20
        (fqfActionCount p * n) (fqfFeatureDim p)
        (fqfQuantileWeights p) (fqfQuantileBias p) features
      values = qSlice32 (action * n) n allValues
  in mkFQFOutput widths midpoints values
{-# COMPILE AGDA2HS fqfForward #-}

fqfActionMean : FQFOutput → Q20
fqfActionMean o = MkQ20 (fqfMeanQ20 (fqfWidths o) (fqfValues o))
{-# COMPILE AGDA2HS fqfActionMean #-}

------------------------------------------------------------------------
-- Factorized NoisyNet actor only; critic is deterministic
------------------------------------------------------------------------

record ActorParams : Set where
  constructor mkActorParams
  field
    actorFeatureDim : Int32
    actorActionCount : Int32
    actorMuWeights : Vec32
    actorSigmaWeights : Vec32
    actorMuBias : Vec32
    actorSigmaBias : Vec32

open ActorParams public
{-# COMPILE AGDA2HS ActorParams #-}

record ActorNoiseState : Set where
  constructor mkActorNoiseState
  field
    actorNoiseSeed : Word64
    actorNoiseRemaining : Int32
    actorInputFactors : Vec32
    actorOutputFactors : Vec32

open ActorNoiseState public
{-# COMPILE AGDA2HS ActorNoiseState #-}

actorNoiseInit : Word64 → Int32 → Int32 → ActorNoiseState
actorNoiseInit seed inputDim actionCount =
  let nextSeed = qWord64Next seed
  in mkActorNoiseState nextSeed (qNoiseDuration seed)
       (qNormalNoiseVec seed inputDim)
       (qNormalNoiseVec nextSeed actionCount)
{-# COMPILE AGDA2HS actorNoiseInit #-}

actorNoiseAdvance : Int32 → Int32 → ActorNoiseState → ActorNoiseState
actorNoiseAdvance inputDim actionCount n =
  if int32GreaterThanOne (actorNoiseRemaining n)
  then mkActorNoiseState (qWord64Next (actorNoiseSeed n))
         (int32Decrement (actorNoiseRemaining n))
         (actorInputFactors n) (actorOutputFactors n)
  else actorNoiseInit (actorNoiseSeed n) inputDim actionCount
{-# COMPILE AGDA2HS actorNoiseAdvance #-}

actorLogits : ActorParams → ActorNoiseState → Vec32 → Vec32
actorLogits p n features =
  qFactorizedNoisyLinear
    (actorActionCount p) (actorFeatureDim p)
    (actorMuWeights p) (actorSigmaWeights p)
    (actorMuBias p) (actorSigmaBias p)
    features (actorInputFactors n) (actorOutputFactors n)
{-# COMPILE AGDA2HS actorLogits #-}

actorProbabilities : ActorParams → ActorNoiseState → Vec32 → Vec32
actorProbabilities p n features =
  q4Softmax 131072 (actorLogits p n features)
{-# COMPILE AGDA2HS actorProbabilities #-}

actorChooseAction : ActorParams → ActorNoiseState → Vec32 → Int32
actorChooseAction p n features =
  qGumbelMaxSelect (actorNoiseSeed n) 131072 (actorLogits p n features)
{-# COMPILE AGDA2HS actorChooseAction #-}

------------------------------------------------------------------------
-- Three-step sampled on-policy SARSA; lambda = 0, gamma = 0.99
------------------------------------------------------------------------

sarsa3Target
  : Q20 → Q20 → Q20
  → Int32 → Int32 → Int32
  → Vec32 → Vec32
sarsa3Target r0 r1 r2 terminal0 terminal1 terminal2 bootstrap =
  qSarsa3Target (rawQ20 r0) (rawQ20 r1) (rawQ20 r2)
    terminal0 terminal1 terminal2 bootstrap
{-# COMPILE AGDA2HS sarsa3Target #-}

munchausenReward : Q20 → Vec32 → Int32 → Q20
munchausenReward reward probabilities action =
  MkQ20 (qMunchausenReward (rawQ20 reward) (qIndex32 probabilities action))
{-# COMPILE AGDA2HS munchausenReward #-}

l2Gradient : Vec32 → Vec32 → Vec32
l2Gradient = qAddL2Gradient
{-# COMPILE AGDA2HS l2Gradient #-}

------------------------------------------------------------------------
-- Composed recurrent actor-critic network
--
-- Observation -> state-independent-candidate GRU -> [observation, hidden]
-- features -> actor-only factorized NoisyNet -> discrete Gumbel-Max action.
-- A separate deterministic FQF critic evaluates that sampled action.
------------------------------------------------------------------------

record NetworkParams : Set where
  constructor mkNetworkParams
  field
    networkGRUParams : GRUParams
    networkFQFParams : FQFParams
    networkActorParams : ActorParams

open NetworkParams public
{-# COMPILE AGDA2HS NetworkParams #-}

record NetworkState : Set where
  constructor mkNetworkState
  field
    networkHiddenState : Vec32
    networkActorNoiseState : ActorNoiseState

open NetworkState public
{-# COMPILE AGDA2HS NetworkState #-}

record NetworkStep : Set where
  constructor mkNetworkStep
  field
    networkNextState : NetworkState
    networkFeatureVector : Vec32
    networkPolicyProbabilities : Vec32
    networkSelectedAction : Int32
    networkSelectedActionDistribution : FQFOutput
    networkSelectedActionValue : Q20

open NetworkStep public
{-# COMPILE AGDA2HS NetworkStep #-}

-- Dimension invariant:
-- actorFeatureDim == fqfFeatureDim == gruInputDim + gruHiddenDim.
-- Weight arrays must match the row-major dimensions declared by each head.
networkInitialState : NetworkParams → Word64 → NetworkState
networkInitialState p seed =
  let gru = networkGRUParams p
      actor = networkActorParams p
      hidden = qZeroVec32 (gruHiddenDim gru)
      noise = actorNoiseInit seed (actorFeatureDim actor) (actorActionCount actor)
  in mkNetworkState hidden noise
{-# COMPILE AGDA2HS networkInitialState #-}

-- One causal recurrent inference step. The noise state is consumed only by
-- the actor and advanced after selection; GRU and FQF critic remain deterministic.
networkStep : NetworkParams → NetworkState → Vec32 → NetworkStep
networkStep p state observation =
  let gru = networkGRUParams p
      critic = networkFQFParams p
      actor = networkActorParams p
      hidden' = gruStep gru observation (networkHiddenState state)
      features = qAppend32 observation hidden'
      actorNoise = networkActorNoiseState state
      logits = actorLogits actor actorNoise features
      probabilities = q4Softmax 131072 logits
      action = qGumbelMaxSelect (actorNoiseSeed actorNoise) 131072 logits
      distribution = fqfForward critic features action
      actionValue = fqfActionMean distribution
      nextNoise = actorNoiseAdvance
        (actorFeatureDim actor) (actorActionCount actor) actorNoise
      nextState = mkNetworkState hidden' nextNoise
  in mkNetworkStep nextState features probabilities action distribution actionValue
{-# COMPILE AGDA2HS networkStep #-}

-- Evaluation for an externally supplied behavior action. The recurrent
-- transition and actor-noise clock advance once, independent of action source.
networkStepForAction : NetworkParams → NetworkState → Vec32 → Int32 → NetworkStep
networkStepForAction p state observation action =
  let gru = networkGRUParams p
      critic = networkFQFParams p
      actor = networkActorParams p
      hidden' = gruStep gru observation (networkHiddenState state)
      features = qAppend32 observation hidden'
      actorNoise = networkActorNoiseState state
      probabilities = actorProbabilities actor actorNoise features
      distribution = fqfForward critic features action
      actionValue = fqfActionMean distribution
      nextNoise = actorNoiseAdvance
        (actorFeatureDim actor) (actorActionCount actor) actorNoise
      nextState = mkNetworkState hidden' nextNoise
  in mkNetworkStep nextState features probabilities action distribution actionValue
{-# COMPILE AGDA2HS networkStepForAction #-}

-- The bootstrap distribution must come from the behavior action sampled at
-- step three. This deliberately exposes no max-Q or greedy-backup operation.
networkSarsa3Target
  : Q20 → Q20 → Q20
  → Int32 → Int32 → Int32
  → NetworkStep → Vec32
networkSarsa3Target r0 r1 r2 terminal0 terminal1 terminal2 bootstrap =
  sarsa3Target r0 r1 r2 terminal0 terminal1 terminal2
    (fqfValues (networkSelectedActionDistribution bootstrap))
{-# COMPILE AGDA2HS networkSarsa3Target #-}

record DistributionalTarget : Set where
  constructor mkDistributionalTarget
  field
    distributionalTargetWidths : Vec32
    distributionalTargetValues : Vec32

open DistributionalTarget public
{-# COMPILE AGDA2HS DistributionalTarget #-}

-- A scalar n-step reward shift preserves the bootstrap quantile fractions.
networkSarsa3DistributionalTarget
  : Q20 → Q20 → Q20
  → Int32 → Int32 → Int32
  → NetworkStep → DistributionalTarget
networkSarsa3DistributionalTarget r0 r1 r2 terminal0 terminal1 terminal2 bootstrap =
  let bootstrapDistribution = networkSelectedActionDistribution bootstrap
      targetValues = sarsa3Target r0 r1 r2 terminal0 terminal1 terminal2
        (fqfValues bootstrapDistribution)
  in mkDistributionalTarget
       (fqfWidths bootstrapDistribution) targetValues
{-# COMPILE AGDA2HS networkSarsa3DistributionalTarget #-}

networkMunchausenReward : Q20 → NetworkStep → Q20
networkMunchausenReward reward decision =
  munchausenReward reward
    (networkPolicyProbabilities decision) (networkSelectedAction decision)
{-# COMPILE AGDA2HS networkMunchausenReward #-}


------------------------------------------------------------------------
-- Shared reverse-mode kernels
--
-- These VJPs differentiate the smooth Q20 shadow. Integer rounding,
-- saturation, table quantization, actor noise samples, and Gumbel-Max
-- selection are treated as fixed/discrete boundaries.
------------------------------------------------------------------------

record LinearCotangent : Set where
  constructor mkLinearCotangent
  field
    linearWeightCotangent : Vec32
    linearBiasCotangent : Vec32
    linearInputCotangent : Vec32

open LinearCotangent public
{-# COMPILE AGDA2HS LinearCotangent #-}

linearRowsVJP
  : Int32 → Int32 → Vec32 → Vec32 → Vec32 → Vec32
  → LinearCotangent
linearRowsVJP rows cols weights bias input outputDirection =
  let packed = qLinearRowsVJP rows cols weights bias input outputDirection
      weightCount = qVecLength weights
      biasCount = qVecLength bias
      inputStart = addInt32 weightCount biasCount
  in mkLinearCotangent
       (qSlice32 0 weightCount packed)
       (qSlice32 weightCount biasCount packed)
       (qSlice32 inputStart cols packed)
{-# COMPILE AGDA2HS linearRowsVJP #-}

record NoisyLinearCotangent : Set where
  constructor mkNoisyLinearCotangent
  field
    noisyMuWeightCotangent : Vec32
    noisySigmaWeightCotangent : Vec32
    noisyMuBiasCotangent : Vec32
    noisySigmaBiasCotangent : Vec32
    noisyInputCotangent : Vec32

open NoisyLinearCotangent public
{-# COMPILE AGDA2HS NoisyLinearCotangent #-}

noisyLinearVJP
  : Int32 → Int32
  → Vec32 → Vec32 → Vec32 → Vec32
  → Vec32 → Vec32 → Vec32 → Vec32
  → NoisyLinearCotangent
noisyLinearVJP rows cols muWeights sigmaWeights muBias sigmaBias
  input inputNoise outputNoise outputDirection =
  let packed = qFactorizedNoisyLinearVJP rows cols
        muWeights sigmaWeights muBias sigmaBias
        input inputNoise outputNoise outputDirection
      muWeightCount = qVecLength muWeights
      sigmaWeightCount = qVecLength sigmaWeights
      muBiasCount = qVecLength muBias
      sigmaBiasCount = qVecLength sigmaBias
      sigmaWeightStart = muWeightCount
      muBiasStart = addInt32 sigmaWeightStart sigmaWeightCount
      sigmaBiasStart = addInt32 muBiasStart muBiasCount
      inputStart = addInt32 sigmaBiasStart sigmaBiasCount
  in mkNoisyLinearCotangent
       (qSlice32 0 muWeightCount packed)
       (qSlice32 sigmaWeightStart sigmaWeightCount packed)
       (qSlice32 muBiasStart muBiasCount packed)
       (qSlice32 sigmaBiasStart sigmaBiasCount packed)
       (qSlice32 inputStart cols packed)
{-# COMPILE AGDA2HS noisyLinearVJP #-}

record GRUCotangent : Set where
  constructor mkGRUCotangent
  field
    gruGateWeightCotangent : Vec32
    gruGateBiasCotangent : Vec32
    gruCandidateWeightCotangent : Vec32
    gruCandidateBiasCotangent : Vec32
    gruPreviousCotangent : Vec32
    gruInputCotangent : Vec32

open GRUCotangent public
{-# COMPILE AGDA2HS GRUCotangent #-}

gruStepVJP : GRUParams → Vec32 → Vec32 → Vec32 → GRUCotangent
gruStepVJP p input previous outputDirection =
  let hiddenDim = gruHiddenDim p
      inputDim = gruInputDim p
      gatePre = qLinearRowsQ20 hiddenDim inputDim
        (gruGateWeights p) (gruGateBias p) input
      gate = qShiftedGateVec gatePre
      candidate = qLinearRowsQ20 hiddenDim inputDim
        (gruCandidateWeights p) (gruCandidateBias p) input
      mixed = qConvexMix gate previous candidate
      normalized = qMadLayerNorm mixed
      normalizedDirection = qSoftsignVJP normalized outputDirection
      mixedDirection = qMadLayerNormVJP mixed normalizedDirection
      mixDirections = qConvexMixVJP gate previous candidate mixedDirection
      gateDirection = qShiftedGateVJP gatePre
        (qSlice32 0 hiddenDim mixDirections)
      previousDirection = qSlice32 hiddenDim hiddenDim mixDirections
      candidateDirection = qSlice32 (hiddenDim + hiddenDim) hiddenDim mixDirections
      gateLinear = linearRowsVJP hiddenDim inputDim
        (gruGateWeights p) (gruGateBias p) input gateDirection
      candidateLinear = linearRowsVJP hiddenDim inputDim
        (gruCandidateWeights p) (gruCandidateBias p) input candidateDirection
  in mkGRUCotangent
       (linearWeightCotangent gateLinear)
       (linearBiasCotangent gateLinear)
       (linearWeightCotangent candidateLinear)
       (linearBiasCotangent candidateLinear)
       previousDirection
       (qAddVec32 (linearInputCotangent gateLinear)
                  (linearInputCotangent candidateLinear))
{-# COMPILE AGDA2HS gruStepVJP #-}

record ActorCotangent : Set where
  constructor mkActorCotangent
  field
    actorMuWeightCotangent : Vec32
    actorSigmaWeightCotangent : Vec32
    actorMuBiasCotangent : Vec32
    actorSigmaBiasCotangent : Vec32
    actorFeatureCotangent : Vec32

open ActorCotangent public
{-# COMPILE AGDA2HS ActorCotangent #-}

actorLogProbabilityVJP
  : ActorParams → ActorNoiseState → Vec32 → Int32 → Int32
  → ActorCotangent
actorLogProbabilityVJP p noise features action advantage =
  let logits = actorLogits p noise features
      probabilities = q4Softmax 131072 logits
      logProbabilityDirection = qLogProbabilityCotangent action probabilities
      logitsDirection = q4SoftmaxVJP 131072 logits probabilities
        logProbabilityDirection
      scaledDirection = qScaleVec32 advantage logitsDirection
      linear = noisyLinearVJP
        (actorActionCount p) (actorFeatureDim p)
        (actorMuWeights p) (actorSigmaWeights p)
        (actorMuBias p) (actorSigmaBias p)
        features (actorInputFactors noise) (actorOutputFactors noise)
        scaledDirection
  in mkActorCotangent
       (noisyMuWeightCotangent linear)
       (noisySigmaWeightCotangent linear)
       (noisyMuBiasCotangent linear)
       (noisySigmaBiasCotangent linear)
       (noisyInputCotangent linear)
{-# COMPILE AGDA2HS actorLogProbabilityVJP #-}

record FQFCotangent : Set where
  constructor mkFQFCotangent
  field
    fqfFractionWeightCotangent : Vec32
    fqfFractionBiasCotangent : Vec32
    fqfQuantileWeightCotangent : Vec32
    fqfQuantileBiasCotangent : Vec32
    fqfFeatureCotangent : Vec32

open FQFCotangent public
{-# COMPILE AGDA2HS FQFCotangent #-}

fqfActionVJP
  : FQFParams → Vec32 → Int32 → Vec32 → FQFCotangent
fqfActionVJP p features action quantileDirection =
  let quantileCount = int32Sixteen
      fractionLogits = qLinearRowsQ20 quantileCount (fqfFeatureDim p)
        (fqfFractionWeights p) (fqfFractionBias p) features
      widths = q4Softmax 1048576 fractionLogits
      midpoints = qPrefixMidpoints widths
      quantileRows = fqfActionCount p * quantileCount
      allValues = qLinearRowsQ20 quantileRows (fqfFeatureDim p)
        (fqfQuantileWeights p) (fqfQuantileBias p) features
      selectedValues = qSlice32 (action * quantileCount)
        quantileCount allValues
      allValueDirection = qEmbedActionCotangent action quantileCount
        (fqfActionCount p) quantileDirection
      quantileLinear = linearRowsVJP quantileRows (fqfFeatureDim p)
        (fqfQuantileWeights p) (fqfQuantileBias p)
        features allValueDirection
      -- Boundary proposal uses the piecewise-linear quantile shadow.
      fractionDirection = qFQFFractionLogitDirection
        fractionLogits widths midpoints selectedValues
      fractionLinear = linearRowsVJP quantileCount (fqfFeatureDim p)
        (fqfFractionWeights p) (fqfFractionBias p)
        features fractionDirection
  in mkFQFCotangent
       (linearWeightCotangent fractionLinear)
       (linearBiasCotangent fractionLinear)
       (linearWeightCotangent quantileLinear)
       (linearBiasCotangent quantileLinear)
       (qAddVec32 (linearInputCotangent fractionLinear)
                  (linearInputCotangent quantileLinear))
{-# COMPILE AGDA2HS fqfActionVJP #-}

record NetworkPullback : Set where
  constructor mkNetworkPullback
  field
    networkParameterDirection : Vec32
    networkPreviousHiddenDirection : Vec32
    networkObservationDirection : Vec32

open NetworkPullback public
{-# COMPILE AGDA2HS NetworkPullback #-}

-- Pullback for one selected behavior action. Policy-gradient, FQF quantile,
-- and fraction-proposal directions meet at one shared feature cotangent.
networkStepVJP
  : NetworkParams → NetworkState → Vec32 → Int32 → Int32 → Vec32 → Vec32
  → NetworkPullback
networkStepVJP p state observation action actorAdvantage quantileDirection
  futureHiddenDirection =
  let gru = networkGRUParams p
      critic = networkFQFParams p
      actor = networkActorParams p
      hidden' = gruStep gru observation (networkHiddenState state)
      features = qAppend32 observation hidden'
      actorDirection = actorLogProbabilityVJP actor
        (networkActorNoiseState state) features action actorAdvantage
      criticDirection = fqfActionVJP critic features action quantileDirection
      featureDirection = qAddVec32
        (actorFeatureCotangent actorDirection)
        (fqfFeatureCotangent criticDirection)
      observationCount = qVecLength observation
      hiddenCount = qVecLength hidden'
      directObservationDirection = qSlice32 0 observationCount featureDirection
      hiddenOutputDirection = qAddVec32
        (qSlice32 observationCount hiddenCount featureDirection)
        futureHiddenDirection
      recurrentDirection = gruStepVJP gru observation
        (networkHiddenState state) hiddenOutputDirection
      gruParameters = qAppend32
        (gruGateWeightCotangent recurrentDirection)
        (qAppend32 (gruGateBiasCotangent recurrentDirection)
          (qAppend32 (gruCandidateWeightCotangent recurrentDirection)
                     (gruCandidateBiasCotangent recurrentDirection)))
      criticParameters = qAppend32
        (fqfFractionWeightCotangent criticDirection)
        (qAppend32 (fqfFractionBiasCotangent criticDirection)
          (qAppend32 (fqfQuantileWeightCotangent criticDirection)
                     (fqfQuantileBiasCotangent criticDirection)))
      actorParameters = qAppend32
        (actorMuWeightCotangent actorDirection)
        (qAppend32 (actorSigmaWeightCotangent actorDirection)
          (qAppend32 (actorMuBiasCotangent actorDirection)
                     (actorSigmaBiasCotangent actorDirection)))
  in mkNetworkPullback
       (qAppend32 gruParameters (qAppend32 criticParameters actorParameters))
       (gruPreviousCotangent recurrentDirection)
       (qAddVec32 directObservationDirection
                  (gruInputCotangent recurrentDirection))
{-# COMPILE AGDA2HS networkStepVJP #-}

------------------------------------------------------------------------
-- Parameter vector: one canonical order for CHAD and ObGD
------------------------------------------------------------------------

networkParameterVector : NetworkParams → Vec32
networkParameterVector p =
  let gru = networkGRUParams p
      critic = networkFQFParams p
      actor = networkActorParams p
  in qAppend32 (gruGateWeights gru)
       (qAppend32 (gruGateBias gru)
         (qAppend32 (gruCandidateWeights gru)
           (qAppend32 (gruCandidateBias gru)
             (qAppend32 (fqfFractionWeights critic)
               (qAppend32 (fqfFractionBias critic)
                 (qAppend32 (fqfQuantileWeights critic)
                   (qAppend32 (fqfQuantileBias critic)
                     (qAppend32 (actorMuWeights actor)
                       (qAppend32 (actorSigmaWeights actor)
                         (qAppend32 (actorMuBias actor)
                                    (actorSigmaBias actor)))))))))))
{-# COMPILE AGDA2HS networkParameterVector #-}

networkWithParameterVector : NetworkParams → Vec32 → NetworkParams
networkWithParameterVector p flat =
  let gru = networkGRUParams p
      critic = networkFQFParams p
      actor = networkActorParams p
      gwN = qVecLength (gruGateWeights gru)
      gbN = qVecLength (gruGateBias gru)
      cwN = qVecLength (gruCandidateWeights gru)
      cbN = qVecLength (gruCandidateBias gru)
      fwN = qVecLength (fqfFractionWeights critic)
      fbN = qVecLength (fqfFractionBias critic)
      qwN = qVecLength (fqfQuantileWeights critic)
      qbN = qVecLength (fqfQuantileBias critic)
      awN = qVecLength (actorMuWeights actor)
      asN = qVecLength (actorSigmaWeights actor)
      abN = qVecLength (actorMuBias actor)
      axN = qVecLength (actorSigmaBias actor)
      o1 = gwN
      o2 = o1 + gbN
      o3 = o2 + cwN
      o4 = o3 + cbN
      o5 = o4 + fwN
      o6 = o5 + fbN
      o7 = o6 + qwN
      o8 = o7 + qbN
      o9 = o8 + awN
      o10 = o9 + asN
      o11 = o10 + abN
      o12 = o11 + axN
      gru' = mkGRUParams (gruInputDim gru) (gruHiddenDim gru)
        (qSlice32 0 gwN flat) (qSlice32 o1 gbN flat)
        (qSlice32 o2 cwN flat) (qSlice32 o3 cbN flat)
      critic' = mkFQFParams (fqfFeatureDim critic) (fqfActionCount critic)
        (qSlice32 o4 fwN flat) (qSlice32 o5 fbN flat)
        (qSlice32 o6 qwN flat) (qSlice32 o7 qbN flat)
      actor' = mkActorParams (actorFeatureDim actor) (actorActionCount actor)
        (qSlice32 o8 awN flat) (qSlice32 o9 asN flat)
        (qSlice32 o10 abN flat) (qSlice32 o11 axN flat)
  in mkNetworkParams gru' critic' actor'
{-# COMPILE AGDA2HS networkWithParameterVector #-}

------------------------------------------------------------------------
-- Finite iterative CHAD: forward trace and state-passed reverse scan
------------------------------------------------------------------------

record CHADForwardStep (S Y : Set) : Set where
  constructor mkCHADForwardStep
  field
    chadNextState : S
    chadOutput : Y

open CHADForwardStep public
{-# COMPILE AGDA2HS CHADForwardStep #-}

record CHADPullbackStep (DP DS DX : Set) : Set where
  constructor mkCHADPullbackStep
  field
    chadParameterDirection : DP
    chadPreviousStateDirection : DS
    chadInputDirection : DX

open CHADPullbackStep public
{-# COMPILE AGDA2HS CHADPullbackStep #-}

record IterativeCHADCell
  (P S X Y DP DS DY DX : Set) : Set where
  constructor mkIterativeCHADCell
  field
    chadForwardCell : P → S → X → CHADForwardStep S Y
    chadPullbackCell : P → S → X → Y → DS → DY → CHADPullbackStep DP DS DX
    chadZeroParameterDirection : P → DP
    chadAddParameterDirections : DP → DP → DP

open IterativeCHADCell public
{-# COMPILE AGDA2HS IterativeCHADCell #-}

data CHADTrace (S X Y : Set) : (@0 n : Nat) → Set where
  chadEmpty : CHADTrace S X Y zero
  chadCons : ∀ {@0 n} → S → X → Y → CHADTrace S X Y n
          → CHADTrace S X Y (suc n)

{-# COMPILE AGDA2HS CHADTrace #-}

record CHADForwardResult (S X Y : Set) (@0 n : Nat) : Set where
  constructor mkCHADForwardResult
  field
    chadFinalState : S
    chadOutputs : Vec Y n
    chadTrace : CHADTrace S X Y n

open CHADForwardResult public
{-# COMPILE AGDA2HS CHADForwardResult #-}

record CHADBackwardResult (DP DS DX : Set) (@0 n : Nat) : Set where
  constructor mkCHADBackwardResult
  field
    chadAccumulatedParameterDirection : DP
    chadInitialStateDirection : DS
    chadInputDirections : Vec DX n

open CHADBackwardResult public
{-# COMPILE AGDA2HS CHADBackwardResult #-}

iterativeCHADForward
  : ∀ {P S X Y DP DS DY DX n}
  → IterativeCHADCell P S X Y DP DS DY DX
  → P → S → Vec X n → CHADForwardResult S X Y n
iterativeCHADForward cell p state VNil =
  mkCHADForwardResult state VNil chadEmpty
iterativeCHADForward cell p state (VCons input inputs) =
  let step = chadForwardCell cell p state input
      rest = iterativeCHADForward cell p (chadNextState step) inputs
  in mkCHADForwardResult
       (chadFinalState rest)
       (VCons (chadOutput step) (chadOutputs rest))
       (chadCons state input (chadOutput step) (chadTrace rest))
{-# COMPILE AGDA2HS iterativeCHADForward #-}

iterativeCHADBackward
  : ∀ {P S X Y DP DS DY DX n}
  → IterativeCHADCell P S X Y DP DS DY DX
  → P → CHADTrace S X Y n → Vec DY n → DS
  → CHADBackwardResult DP DS DX n
iterativeCHADBackward cell p chadEmpty VNil terminalDirection =
  mkCHADBackwardResult (chadZeroParameterDirection cell p)
    terminalDirection VNil
iterativeCHADBackward cell p
  (chadCons state input output rest)
  (VCons outputDirection outputDirections) terminalDirection =
  let restResult = iterativeCHADBackward cell p rest
        outputDirections terminalDirection
      local = chadPullbackCell cell p state input output
        (chadInitialStateDirection restResult) outputDirection
  in mkCHADBackwardResult
       (chadAddParameterDirections cell
         (chadParameterDirection local)
         (chadAccumulatedParameterDirection restResult))
       (chadPreviousStateDirection local)
       (VCons (chadInputDirection local) (chadInputDirections restResult))
{-# COMPILE AGDA2HS iterativeCHADBackward #-}

chadTraceLength : ∀ {S X Y n} → CHADTrace S X Y n → Nat
chadTraceLength chadEmpty = zero
chadTraceLength (chadCons state input output rest) =
  suc (chadTraceLength rest)

chadTraceLength-correct
  : ∀ {S X Y n} (trace : CHADTrace S X Y n)
  → chadTraceLength trace ≡ n
chadTraceLength-correct chadEmpty = refl
chadTraceLength-correct (chadCons state input output rest)
  rewrite chadTraceLength-correct rest = refl

------------------------------------------------------------------------
-- The composed network is an iterative CHAD cell
------------------------------------------------------------------------

record NetworkCellInput : Set where
  constructor mkNetworkCellInput
  field
    networkCellObservation : Vec32
    networkCellAction : Int32

open NetworkCellInput public
{-# COMPILE AGDA2HS NetworkCellInput #-}

record NetworkStepCotangent : Set where
  constructor mkNetworkStepCotangent
  field
    networkStepActorAdvantage : Int32
    networkStepQuantileDirection : Vec32

open NetworkStepCotangent public
{-# COMPILE AGDA2HS NetworkStepCotangent #-}

networkCHADCell
  : IterativeCHADCell NetworkParams NetworkState NetworkCellInput
      NetworkStep Vec32 Vec32 NetworkStepCotangent Vec32
networkCHADCell = mkIterativeCHADCell forward backward
  (λ p → qZeroVec32 (qVecLength (networkParameterVector p)))
  qAddVec32
  where
    forward : NetworkParams → NetworkState → NetworkCellInput
            → CHADForwardStep NetworkState NetworkStep
    forward p state sample =
      let step = networkStepForAction p state
            (networkCellObservation sample) (networkCellAction sample)
      in mkCHADForwardStep (networkNextState step) step

    backward : NetworkParams → NetworkState → NetworkCellInput
             → NetworkStep → Vec32 → NetworkStepCotangent
             → CHADPullbackStep Vec32 Vec32 Vec32
    backward p state sample step futureHidden cotangent =
      let direction = networkStepVJP p state
            (networkCellObservation sample) (networkCellAction sample)
            (networkStepActorAdvantage cotangent)
            (networkStepQuantileDirection cotangent)
            futureHidden
      in mkCHADPullbackStep
           (networkParameterDirection direction)
           (networkPreviousHiddenDirection direction)
           (networkObservationDirection direction)
{-# COMPILE AGDA2HS networkCHADCell #-}

record NetworkSequencePullback (@0 n : Nat) : Set where
  constructor mkNetworkSequencePullback
  field
    networkSequenceFinalState : NetworkState
    networkSequenceOutputs : Vec NetworkStep n
    networkSequenceParameterDirection : Vec32
    networkSequenceInitialHiddenDirection : Vec32
    networkSequenceObservationDirections : Vec Vec32 n

open NetworkSequencePullback public
{-# COMPILE AGDA2HS NetworkSequencePullback #-}

networkSequenceVJP
  : ∀ {n}
  → NetworkParams → NetworkState
  → Vec NetworkCellInput n → Vec NetworkStepCotangent n
  → Vec32 → NetworkSequencePullback n
networkSequenceVJP p initial samples outputDirections finalHiddenDirection =
  let forward = iterativeCHADForward networkCHADCell p initial samples
      backward = iterativeCHADBackward networkCHADCell p
        (chadTrace forward) outputDirections finalHiddenDirection
  in mkNetworkSequencePullback
       (chadFinalState forward)
       (chadOutputs forward)
       (chadAccumulatedParameterDirection backward)
       (chadInitialStateDirection backward)
       (chadInputDirections backward)
{-# COMPILE AGDA2HS networkSequenceVJP #-}

------------------------------------------------------------------------
-- Sequential UTD=2 training with one behavior action per observation
--
-- The sample action is supplied by the collector. Each observation causes
-- two parameter updates, while recurrent state and actor-noise time advance
-- exactly once. The smooth pullback feeds an ObGD-bounded gradient trace.
------------------------------------------------------------------------

record NetworkTrainConfig : Set where
  constructor mkNetworkTrainConfig
  field
    networkTrainHuberKappa : Int32
    networkTrainObgdAlpha : Int32
    networkTrainObgdKappa : Int32
    networkTrainTraceDecay : Int32

open NetworkTrainConfig public
{-# COMPILE AGDA2HS NetworkTrainConfig #-}

record NetworkTrainSample : Set where
  constructor mkNetworkTrainSample
  field
    networkTrainObservation : Vec32
    networkTrainAction : Int32
    networkTrainTargetWidths : Vec32
    networkTrainTargetQuantiles : Vec32

open NetworkTrainSample public
{-# COMPILE AGDA2HS NetworkTrainSample #-}

networkTrainCellInputs
  : ∀ {n} → Vec NetworkTrainSample n → Vec NetworkCellInput n
networkTrainCellInputs = mapVec (λ sample →
  mkNetworkCellInput
    (networkTrainObservation sample) (networkTrainAction sample))
{-# COMPILE AGDA2HS networkTrainCellInputs #-}

networkTrainStepCotangents
  : ∀ {n}
  → NetworkTrainConfig
  → Vec NetworkTrainSample n → Vec NetworkStep n
  → Vec NetworkStepCotangent n
networkTrainStepCotangents config VNil VNil = VNil
networkTrainStepCotangents config
  (VCons sample samples) (VCons decision decisions) =
  let distribution = networkSelectedActionDistribution decision
      advantage = subInt32
        (fqfMeanQ20 (networkTrainTargetWidths sample)
          (networkTrainTargetQuantiles sample))
        (rawQ20 (networkSelectedActionValue decision))
      quantileDirection = qQuantileHuberDirection
        (networkTrainHuberKappa config)
        (fqfMidpoints distribution)
        (networkTrainTargetQuantiles sample)
        (fqfValues distribution)
  in VCons (mkNetworkStepCotangent advantage quantileDirection)
       (networkTrainStepCotangents config samples decisions)
{-# COMPILE AGDA2HS networkTrainStepCotangents #-}

-- Full finite-horizon BPTT over a chronological unroll: one forward trace,
-- then one reverse iterative-CHAD scan carrying shared parameter cotangents.
networkTrainSequenceVJP
  : ∀ {n}
  → NetworkTrainConfig → NetworkParams → NetworkState
  → Vec NetworkTrainSample n → NetworkSequencePullback n
networkTrainSequenceVJP config p initial samples =
  let forward = iterativeCHADForward networkCHADCell p initial
        (networkTrainCellInputs samples)
      outputDirections = networkTrainStepCotangents config
        samples (chadOutputs forward)
      backward = iterativeCHADBackward networkCHADCell p
        (chadTrace forward) outputDirections
        (qZeroVec32 (gruHiddenDim (networkGRUParams p)))
  in mkNetworkSequencePullback
       (chadFinalState forward)
       (chadOutputs forward)
       (chadAccumulatedParameterDirection backward)
       (chadInitialStateDirection backward)
       (chadInputDirections backward)
{-# COMPILE AGDA2HS networkTrainSequenceVJP #-}


record NetworkTrainState : Set where
  constructor mkNetworkTrainState
  field
    networkTrainParams : NetworkParams
    networkTrainRuntimeState : NetworkState
    networkTrainObgdTrace : Vec32

open NetworkTrainState public
{-# COMPILE AGDA2HS NetworkTrainState #-}

record NetworkTrainResult : Set where
  constructor mkNetworkTrainResult
  field
    networkTrainNextState : NetworkTrainState
    networkTrainLastStep : NetworkStep
    networkTrainTDAdvantage : Int32
    networkTrainQuantileHuberLoss : Int32
    networkTrainEffectiveAlpha : Int32

open NetworkTrainResult public
{-# COMPILE AGDA2HS NetworkTrainResult #-}

networkTrainInitialState : NetworkParams → NetworkState → NetworkTrainState
networkTrainInitialState p runtime =
  mkNetworkTrainState p runtime
    (qZeroVec32 (qVecLength (networkParameterVector p)))
{-# COMPILE AGDA2HS networkTrainInitialState #-}

networkTrainPass
  : NetworkTrainConfig → NetworkTrainState → NetworkTrainSample
  → NetworkTrainResult
networkTrainPass config state sample =
  let p = networkTrainParams state
      runtime = networkTrainRuntimeState state
      decision = networkStepForAction p runtime
        (networkTrainObservation sample) (networkTrainAction sample)
      distribution = networkSelectedActionDistribution decision
      quantileLoss = qQuantileHuberLoss
        (networkTrainHuberKappa config)
        (fqfMidpoints distribution)
        (networkTrainTargetQuantiles sample)
        (fqfValues distribution)
      quantileDirection = qQuantileHuberDirection
        (networkTrainHuberKappa config)
        (fqfMidpoints distribution)
        (networkTrainTargetQuantiles sample)
        (fqfValues distribution)
      advantage = subInt32
        (fqfMeanQ20 (networkTrainTargetWidths sample)
          (networkTrainTargetQuantiles sample))
        (rawQ20 (networkSelectedActionValue decision))
      cellInput = mkNetworkCellInput
        (networkTrainObservation sample) (networkTrainAction sample)
      outputCotangent = mkNetworkStepCotangent advantage quantileDirection
      oneFrameTrace = chadCons runtime cellInput decision chadEmpty
      oneFrameCotangent = VCons outputCotangent VNil
      reversePass = iterativeCHADBackward networkCHADCell p
        oneFrameTrace oneFrameCotangent
        (qZeroVec32 (gruHiddenDim (networkGRUParams p)))
      regularizedDirection = l2Gradient
        (chadAccumulatedParameterDirection reversePass)
        (networkParameterVector p)
      nextTrace = qTraceAdvance (networkTrainTraceDecay config)
        (networkTrainObgdTrace state) regularizedDirection
      (updatedParameters, effectiveAlpha) = qObgdUpdate
        (networkTrainObgdAlpha config)
        (networkTrainObgdKappa config)
        int32OneQ20
        (networkParameterVector p)
        nextTrace
      p' = networkWithParameterVector p updatedParameters
      state' = mkNetworkTrainState p' (networkNextState decision) nextTrace
  in mkNetworkTrainResult state' decision advantage quantileLoss effectiveAlpha
{-# COMPILE AGDA2HS networkTrainPass #-}

-- Re-evaluate the same transition under the first updated parameters, but
-- retain the original recurrent/noise state so environment time advances once.
networkTrainStepUTD2
  : NetworkTrainConfig → NetworkTrainState → NetworkTrainSample
  → NetworkTrainResult
networkTrainStepUTD2 config state sample =
  let first = networkTrainPass config state sample
      firstState = networkTrainNextState first
      secondInput = mkNetworkTrainState
        (networkTrainParams firstState)
        (networkTrainRuntimeState state)
        (networkTrainObgdTrace firstState)
  in networkTrainPass config secondInput sample
{-# COMPILE AGDA2HS networkTrainStepUTD2 #-}

networkTrainSequenceUTD2
  : ∀ {n}
  → NetworkTrainConfig → NetworkTrainState
  → Vec NetworkTrainSample n → NetworkTrainState
networkTrainSequenceUTD2 config state VNil = state
networkTrainSequenceUTD2 config state (VCons sample samples) =
  let result = networkTrainStepUTD2 config state sample
  in networkTrainSequenceUTD2 config
       (networkTrainNextState result) samples
{-# COMPILE AGDA2HS networkTrainSequenceUTD2 #-}


------------------------------------------------------------------------
-- Multi-step CHAD unroll updates
--
-- These update once per unroll, twice for UTD=2. For UTD=2 per individual
-- transition use networkTrainSequenceUTD2 above (one-step truncation).
------------------------------------------------------------------------

record NetworkTrainChunkResult (@0 n : Nat) : Set where
  constructor mkNetworkTrainChunkResult
  field
    networkTrainChunkNextState : NetworkTrainState
    networkTrainChunkOutputs : Vec NetworkStep n
    networkTrainChunkDirection : Vec32
    networkTrainChunkEffectiveAlpha : Int32

open NetworkTrainChunkResult public
{-# COMPILE AGDA2HS NetworkTrainChunkResult #-}

networkTrainChunkPass
  : ∀ {n}
  → NetworkTrainConfig → NetworkTrainState
  → Vec NetworkTrainSample (suc n)
  → NetworkTrainChunkResult (suc n)
networkTrainChunkPass config state samples =
  let p = networkTrainParams state
      pullback = networkTrainSequenceVJP config p
        (networkTrainRuntimeState state) samples
      direction = l2Gradient
        (networkSequenceParameterDirection pullback)
        (networkParameterVector p)
      nextTrace = qTraceAdvance (networkTrainTraceDecay config)
        (networkTrainObgdTrace state) direction
      (updatedParameters, effectiveAlpha) = qObgdUpdate
        (networkTrainObgdAlpha config)
        (networkTrainObgdKappa config)
        int32OneQ20
        (networkParameterVector p)
        nextTrace
      p' = networkWithParameterVector p updatedParameters
      state' = mkNetworkTrainState p'
        (networkSequenceFinalState pullback) nextTrace
  in mkNetworkTrainChunkResult state'
       (networkSequenceOutputs pullback) direction effectiveAlpha
{-# COMPILE AGDA2HS networkTrainChunkPass #-}

networkTrainChunkUTD2
  : ∀ {n}
  → NetworkTrainConfig → NetworkTrainState
  → Vec NetworkTrainSample (suc n)
  → NetworkTrainChunkResult (suc n)
networkTrainChunkUTD2 config state samples =
  let first = networkTrainChunkPass config state samples
      firstState = networkTrainChunkNextState first
      secondInput = mkNetworkTrainState
        (networkTrainParams firstState)
        (networkTrainRuntimeState state)
        (networkTrainObgdTrace firstState)
  in networkTrainChunkPass config secondInput samples
{-# COMPILE AGDA2HS networkTrainChunkUTD2 #-}

networkTrainChunksUTD2
  : ∀ {m n}
  → NetworkTrainConfig → NetworkTrainState
  → Vec (Vec NetworkTrainSample (suc n)) m
  → NetworkTrainState
networkTrainChunksUTD2 config state VNil = state
networkTrainChunksUTD2 config state (VCons samples rest) =
  let result = networkTrainChunkUTD2 config state samples
  in networkTrainChunksUTD2 config
       (networkTrainChunkNextState result) rest
{-# COMPILE AGDA2HS networkTrainChunksUTD2 #-}


------------------------------------------------------------------------
-- Full-unroll CHAD training. Each non-empty chronological chunk receives
-- two parameter updates; recurrent/noise time advances once per chunk.
------------------------------------------------------------------------

