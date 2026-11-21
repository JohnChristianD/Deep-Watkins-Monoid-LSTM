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
qAddL2GradientRaw gradient weights =
  U.zipWith (\g w ->
    satInt32 (fromIntegral g + fromIntegral (qMulRaw 16 w)))
    gradient weights

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
qNormalNoiseVec = qNormalNoiseVecRaw
qNoiseDuration = qNoiseDurationRaw
qWord64Next = pcgAdvanceRaw
qFactorizedNoisyLinear = qFactorizedNoisyLinearRaw
qGumbelMaxSelect = qGumbelMaxSelectRaw
qMunchausenReward = qMunchausenRewardRaw
qSarsa3Target = qSarsa3TargetRaw
qAddL2Gradient = qAddL2GradientRaw
#-}

postulate
  Int32 Int64 Word32 Word64 Int8 : Set
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
{-# COMPILE AGDA2HS qNormalNoiseVec #-}
{-# COMPILE AGDA2HS qNoiseDuration #-}
{-# COMPILE AGDA2HS qWord64Next #-}
{-# COMPILE AGDA2HS qFactorizedNoisyLinear #-}
{-# COMPILE AGDA2HS qGumbelMaxSelect #-}
{-# COMPILE AGDA2HS qMunchausenReward #-}
{-# COMPILE AGDA2HS qSarsa3Target #-}
{-# COMPILE AGDA2HS qAddL2Gradient #-}
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
    fqfQuantileCount : Int32
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
  let n = fqfQuantileCount p
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

