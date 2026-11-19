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
#-}

------------------------------------------------------------------------
-- Canonical learner semantics.
------------------------------------------------------------------------

module FullCoupled.CanonicalLearnerMonolith where

-- Merged external import surface; internal FullCoupled imports remain module-local.
-- The agda2hs base library provides the Haskell-facing Prelude,
-- including Haskell.Prim's core types, equality, and Double.
-- Numeric/vector kernels use Csimma's postulate + FOREIGN AGDA2HS boundary;
-- the executable result carries an erased S0 simulation witness.
-- This model has a Haskell extraction boundary, but no C/C++ pointer/event
-- boundary: IORef, Ptr, StablePtr, C types, MVar, and CFuture adapters do not
-- belong in its recurrent kernel.
--
open import Haskell.Prelude public

{-# FOREIGN AGDA2HS
{-# LANGUAGE BangPatterns #-}
import qualified Data.Bits as Bits
import Data.Int (Int64)
import Data.Word (Word64)
import Data.Vector.Unboxed (Vector)
import qualified Data.Vector.Unboxed as VU

type Vec64 = Vector Int64
type VecD = Vector Double

dZero, dOne, dTwo, dEight, dEpsilon :: Double
dZero = 0.0
dOne = 1.0
dTwo = 2.0
dEight = 8.0
dEpsilon = 1.0 / 1024.0

dAdd, dSub, dMul, dDiv :: Double -> Double -> Double
dAdd = (+)
dSub = (-)
dMul = (*)
dDiv = (/)

dNegate :: Double -> Double
dNegate = negate

dLess :: Double -> Double -> Bool
dLess = (<)

dSqrt :: Double -> Double
dSqrt = sqrt

lit64 :: Integer -> Int64
lit64 = fromIntegral

add64, sub64, mul64, shiftL64, shiftR64, and64, xor64 :: Int64 -> Int64 -> Int64
add64 = (+)
sub64 = (-)
mul64 = (*)
shiftL64 x s = Bits.unsafeShiftL x (fromIntegral s)
shiftR64 x s = Bits.unsafeShiftR x (fromIntegral s)
and64 = (Bits..&.)
xor64 = Bits.xor

clz64 :: Int64 -> Int64
clz64 x = fromIntegral (Bits.countLeadingZeros (fromIntegral x :: Word64))

eq64, gt64, lt64, ge64, le64 :: Int64 -> Int64 -> Bool
eq64 = (==)
gt64 = (>)
lt64 = (<)
ge64 = (>=)
le64 = (<=)

vLen64 :: Vector Int64 -> Int64
vLen64 = fromIntegral . VU.length

vAt64 :: Vector Int64 -> Int64 -> Int64
vAt64 v i = VU.unsafeIndex v (fromIntegral i)

vGen64 :: Int64 -> (Int64 -> Int64) -> Vector Int64
vGen64 n f = VU.generate (fromIntegral n) (f . fromIntegral)

vMap64 :: (Int64 -> Int64) -> Vector Int64 -> Vector Int64
vMap64 = VU.map

vAppend64 :: Vector Int64 -> Vector Int64 -> Vector Int64
vAppend64 = (VU.++)

vFoldlIdx64 :: (Int64 -> Int64 -> Int64 -> Int64) -> Int64 -> Vector Int64 -> Int64
vFoldlIdx64 f = VU.ifoldl' (\acc i v -> f acc (fromIntegral i) v)

quot64, rem64 :: Int64 -> Int64 -> Int64
quot64 = quot
rem64 = rem

i64ToDouble :: Int64 -> Double
i64ToDouble = fromIntegral

q20ToDouble :: Int64 -> Double
q20ToDouble x = fromIntegral x / 1048576.0

doubleToQ20 :: Double -> Int64
doubleToQ20 x = fromIntegral (round (x * 1048576.0) :: Integer)

vec64ToD :: Vector Int64 -> Vector Double
vec64ToD = VU.map q20ToDouble

vecDTo64 :: Vector Double -> Vector Int64
vecDTo64 = VU.map doubleToQ20

vDLen :: Vector Double -> Int64
vDLen = fromIntegral . VU.length

vDAt :: Vector Double -> Int64 -> Double
vDAt v i = VU.unsafeIndex v (fromIntegral i)

vDGen :: Int64 -> (Int64 -> Double) -> Vector Double
vDGen n f = VU.generate (fromIntegral n) (f . fromIntegral)

vDFoldlIdx :: (Double -> Int64 -> Double -> Double) -> Double -> Vector Double -> Double
vDFoldlIdx f = VU.ifoldl' (\\acc i v -> f acc (fromIntegral i) v)
#-}

postulate
  Int64 Vec64 : Set
  lit64       : Integer → Int64
  add64 sub64 mul64 shiftL64 shiftR64 and64 xor64 : Int64 → Int64 → Int64
  clz64       : Int64 → Int64
  eq64 gt64 lt64 ge64 le64 : Int64 → Int64 → Bool
  vLen64      : Vec64 → Int64
  vAt64       : Vec64 → Int64 → Int64
  vGen64      : Int64 → (Int64 → Int64) → Vec64
  vMap64      : (Int64 → Int64) → Vec64 → Vec64
  vAppend64   : Vec64 → Vec64 → Vec64
  vFoldlIdx64 : (Int64 → Int64 → Int64 → Int64) → Int64 → Vec64 → Int64
  VecD : Set
  quot64 rem64 : Int64 → Int64 → Int64
  i64ToDouble q20ToDouble : Int64 → Double
  doubleToQ20 : Double → Int64
  vec64ToD : Vec64 → VecD
  vecDTo64 : VecD → Vec64
  vDLen : VecD → Int64
  vDAt : VecD → Int64 → Double
  vDGen : Int64 → (Int64 → Double) → VecD
  vDFoldlIdx : (Double → Int64 → Double → Double) → Double → VecD → Double
  dZero dOne dTwo dEight dEpsilon : Double
  dAdd dSub dMul dDiv : Double → Double → Double
  dNegate : Double → Double
  dLess : Double → Double → Bool
  dSqrt : Double → Double

------------------------------------------------------------------------
-- Exact O(1) Q44.20 Dyadic Constants (Strict Single Fixed Precision)
------------------------------------------------------------------------

qShift64 qOne64 qHalf64 qMask20 lrBase64 betaStream64 gammaQ64 : Int64
qShift64     = lit64 20
qOne64       = lit64 1048576
qHalf64      = lit64 524288
qMask20      = lit64 1048575
lrBase64     = lit64 65536      -- 1/16
betaStream64 = lit64 1048524    -- 0.99995
gammaQ64     = lit64 1048524    -- 0.99995
{-# COMPILE AGDA2HS qShift64 #-}
{-# COMPILE AGDA2HS qHalf64 #-}
{-# COMPILE AGDA2HS qOne64 #-}
{-# COMPILE AGDA2HS qMask20 #-}
{-# COMPILE AGDA2HS lrBase64 #-}
{-# COMPILE AGDA2HS betaStream64 #-}
{-# COMPILE AGDA2HS gammaQ64 #-}

------------------------------------------------------------------------
-- Branchless Split-Half Q44.20 ALU + 4-Bin Padé-Newton Reciprocal
------------------------------------------------------------------------

abs64 : Int64 → Int64
abs64 x = let m = shiftR64 x (lit64 63) in sub64 (xor64 x m) m
{-# COMPILE AGDA2HS abs64 #-}

sign64 : Int64 → Int64
sign64 x =
  sub64 (if gt64 x (lit64 0) then lit64 1 else lit64 0)
        (if lt64 x (lit64 0) then lit64 1 else lit64 0)
{-# COMPILE AGDA2HS sign64 #-}

max64 : Int64 → Int64 → Int64
max64 a b = let d = sub64 a b in sub64 a (and64 d (shiftR64 d (lit64 63)))
{-# COMPILE AGDA2HS max64 #-}

min64 : Int64 → Int64 → Int64
min64 a b = let d = sub64 a b in add64 b (and64 d (shiftR64 d (lit64 63)))
{-# COMPILE AGDA2HS min64 #-}

clamp64 : Int64 → Int64 → Int64 → Int64
clamp64 x lo hi = min64 (max64 x lo) hi
{-# COMPILE AGDA2HS clamp64 #-}

relu64 : Int64 → Int64
relu64 x = max64 x (lit64 0)
{-# COMPILE AGDA2HS relu64 #-}

splitMulQ20 : Int64 → Int64 → Int64
splitMulQ20 a b =
  let aa  = abs64 a
      bb  = abs64 b
      ah  = shiftR64 aa (lit64 20)
      al  = and64 aa qMask20
      bh  = shiftR64 bb (lit64 20)
      bl  = and64 bb qMask20
      mag = add64 (add64 (shiftL64 (mul64 ah bh) (lit64 20)) (mul64 ah bl))
                  (add64 (mul64 al bh) (shiftR64 (mul64 al bl) (lit64 20)))
  in if lt64 (xor64 a b) (lit64 0) then sub64 (lit64 0) mag else mag
{-# COMPILE AGDA2HS splitMulQ20 #-}

padeMid4 padeC04 padeC14 : Int64 → Int64
padeMid4 b =
  if eq64 b (lit64 0) then lit64 1179648
  else if eq64 b (lit64 1) then lit64 1441792
  else if eq64 b (lit64 2) then lit64 1703936
  else lit64 1966080
padeC04 b =
  if eq64 b (lit64 0) then lit64 932068
  else if eq64 b (lit64 1) then lit64 762601
  else if eq64 b (lit64 2) then lit64 645278
  else lit64 559241
padeC14 b =
  if eq64 b (lit64 0) then lit64 828505
  else if eq64 b (lit64 1) then lit64 554619
  else if eq64 b (lit64 2) then lit64 397094
  else lit64 298262
{-# COMPILE AGDA2HS padeMid4 #-}
{-# COMPILE AGDA2HS padeC04 #-}
{-# COMPILE AGDA2HS padeC14 #-}

mulRecipPade1 : Int64 → Int64 → Int64
mulRecipPade1 x d =
  if eq64 d (lit64 0) then lit64 0
  else
    let s    = mul64 (sign64 x) (sign64 d)
        ax   = abs64 x
        ad   = abs64 d
        b    = sub64 (lit64 63) (clz64 ad)
        sh   = sub64 b qShift64
        m    = if ge64 sh (lit64 0) then shiftR64 ad sh else shiftL64 ad (sub64 (lit64 0) sh)
        bin  = and64 (shiftR64 (sub64 m qOne64) (lit64 18)) (lit64 3)
        t    = sub64 m (padeMid4 bin)
        y0   = sub64 (padeC04 bin) (splitMulQ20 (padeC14 bin) t)
        two  = shiftL64 (lit64 2) (lit64 20)
        y1   = splitMulQ20 y0 (sub64 two (splitMulQ20 m y0))
        prod = splitMulQ20 ax y1
    in mul64 s (if ge64 sh (lit64 0) then shiftR64 prod sh else shiftL64 prod (sub64 (lit64 0) sh))
{-# COMPILE AGDA2HS mulRecipPade1 #-}

invSqrtQ20 : Int64 → Int64
invSqrtQ20 v =
  if le64 v (lit64 0) then qOne64
  else
    let b   = sub64 (lit64 63) (clz64 v)
        e   = sub64 b qShift64
        h   = if ge64 e (lit64 0) then shiftR64 e (lit64 1)
              else sub64 (lit64 0) (shiftR64 (add64 (sub64 (lit64 0) e) (lit64 1)) (lit64 1))
        sh  = mul64 (lit64 2) h
        m   = if ge64 sh (lit64 0) then shiftR64 v sh else shiftL64 v (sub64 (lit64 0) sh)
        ms  = if le64 m (lit64 0) then qOne64 else m
        t   = sub64 ms (shiftL64 (lit64 2) (lit64 20))
        y0  = add64 (sub64 (lit64 741455) (splitMulQ20 (lit64 185364) t))
                    (splitMulQ20 (lit64 66200) (splitMulQ20 t t))
        ys  = if lt64 y0 (shiftL64 (lit64 1) (lit64 17)) then shiftL64 (lit64 1) (lit64 18) else y0
        thr = shiftL64 (lit64 3) (lit64 20)
        stp = λ y → shiftR64 (splitMulQ20 y (sub64 thr (splitMulQ20 ms (splitMulQ20 y y)))) (lit64 1)
        y2  = stp (stp ys)
    in if ge64 h (lit64 0) then shiftR64 y2 h else shiftL64 y2 (sub64 (lit64 0) h)
{-# COMPILE AGDA2HS invSqrtQ20 #-}

-- Exact O(log dt) Lazy Per-Action L2 = 2^-16 Catchup w/ Consistent Residue.
-- Int64 exponents are nonnegative signed 64-bit values at this call site.
-- A fixed 64-step structural fuel bound makes the bit loop total in Agda;
-- every positive Int64 reaches zero after at most 63 arithmetic right shifts.
powQ20LoopFuel : Nat → Int64 → Int64 → Int64 → Int64
powQ20LoopFuel zero acc base e = acc
powQ20LoopFuel (suc fuel) acc base e =
  if le64 e (lit64 0) then acc
  else
    let acc'  = if eq64 (and64 e (lit64 1)) (lit64 1) then splitMulQ20 acc base else acc
        base' = splitMulQ20 base base
    in powQ20LoopFuel fuel acc' base' (shiftR64 e (lit64 1))
{-# COMPILE AGDA2HS powQ20LoopFuel #-}

powQ20Loop : Int64 → Int64 → Int64 → Int64
powQ20Loop acc base e = powQ20LoopFuel 64 acc base e
{-# COMPILE AGDA2HS powQ20Loop #-}

decayL2Catchup : Int64 → Int64 → Int64 → Int64 → (Int64 × Int64)
decayL2Catchup dt w rem lr =
  if le64 dt (lit64 0) then (w , rem)
  else if eq64 dt (lit64 1) then
    let tot  = add64 (splitMulQ20 lr w) rem
        smag = shiftR64 (abs64 tot) (lit64 16)
        step = mul64 (sign64 tot) smag
        rem' = sub64 tot (shiftL64 step (lit64 16))
    in (sub64 w step , rem')
  else
    let stepQ = shiftR64 lr (lit64 16)
        baseQ = sub64 qOne64 stepQ
        effD  = sub64 qOne64 (powQ20Loop qOne64 baseQ dt)
        tot   = add64 (shiftL64 (splitMulQ20 effD w) (lit64 16)) rem
        step  = mul64 (sign64 tot) (shiftR64 (abs64 tot) (lit64 16))
        rem'  = sub64 tot (shiftL64 step (lit64 16))
    in (sub64 w step , rem')
{-# COMPILE AGDA2HS decayL2Catchup #-}

------------------------------------------------------------------------
-- WHT Butterfly + À Trous Haar + LayerNorm + 3-Gate Möbius Monoid LSTM
------------------------------------------------------------------------

whtStep32 : Int64 → Vec64 → Vec64
whtStep32 len v =
  vGen64 (lit64 32) (λ i →
    let inHi    = gt64 (and64 i len) (lit64 0)
        partner = xor64 i len
        a       = vAt64 v (if inHi then partner else i)
        b       = vAt64 v (if inHi then i else partner)
    in if inHi then sub64 a b else add64 a b)
{-# COMPILE AGDA2HS whtStep32 #-}

whtButterfly32 : Vec64 → Vec64
whtButterfly32 v0 =
  let v16 = whtStep32 (lit64 16) (whtStep32 (lit64 8) (whtStep32 (lit64 4) (whtStep32 (lit64 2) (whtStep32 (lit64 1) v0))))
  in vMap64 (λ x → shiftR64 x (lit64 3)) v16
{-# COMPILE AGDA2HS whtButterfly32 #-}

atrousPass32 : Int64 → Vec64 → Vec64
atrousPass32 s v =
  vGen64 (lit64 32) (λ i →
    let j = and64 (add64 i s) (lit64 31)
        a = vAt64 v i
        b = vAt64 v j
    in if eq64 (and64 i (lit64 1)) (lit64 0) then shiftR64 (add64 a b) (lit64 1) else shiftR64 (sub64 a b) (lit64 1))
{-# COMPILE AGDA2HS atrousPass32 #-}

atrousHaar32 : Vec64 → Vec64
atrousHaar32 v0 = atrousPass32 (lit64 4) (atrousPass32 (lit64 2) (atrousPass32 (lit64 1) v0))
{-# COMPILE AGDA2HS atrousHaar32 #-}

intLayerNormPow2 : Int64 → Vec64 → Vec64
intLayerNormPow2 sh v =
  let sumV   = vFoldlIdx64 (λ acc _ x → add64 acc x) (lit64 0) v
      meanV  = shiftR64 sumV sh
      varSum = vFoldlIdx64 (λ acc _ x → let d = sub64 x meanV in add64 acc (splitMulQ20 d d)) (lit64 0) v
      invStd = invSqrtQ20 (add64 (shiftR64 varSum sh) (lit64 1024))
  in vMap64 (λ x → splitMulQ20 (sub64 x meanV) invStd) v
{-# COMPILE AGDA2HS intLayerNormPow2 #-}

signReluVec : Vec64 → Vec64
signReluVec = vMap64 (λ x → mul64 (sign64 x) (min64 (abs64 x) qOne64))
{-# COMPILE AGDA2HS signReluVec #-}

shiftedSoftsignQ20 : Int64 → Int64
shiftedSoftsignQ20 z = shiftR64 (add64 qOne64 (mulRecipPade1 z (add64 qOne64 (abs64 z)))) (lit64 1)
{-# COMPILE AGDA2HS shiftedSoftsignQ20 #-}

-- Identity activation for candidate/output paths. Shifted gate transfer
-- functions remain unchanged.
affineIdentityQ20 : Int64 → Int64
affineIdentityQ20 z = z
{-# COMPILE AGDA2HS affineIdentityQ20 #-}

whtAtrousConcat64 : Vec64 → Vec64
whtAtrousConcat64 obs32 =
  let b1 = signReluVec (intLayerNormPow2 (lit64 5) (whtButterfly32 obs32))
      b2 = signReluVec (intLayerNormPow2 (lit64 5) (atrousHaar32 obs32))
  in vAppend64 b1 b2
{-# COMPILE AGDA2HS whtAtrousConcat64 #-}

------------------------------------------------------------------------
-- Csimma's erased product: runtime value plus proof erased by agda2hs.
-- This keeps the compiler-simulation witness attached to executable RNN
-- representation without introducing a second module or runtime payload.
open import Agda.Primitive using (Level; _⊔_)

record S0 {i j : Level} (A : Set i) (@0 P : A → Set j) : Set (i ⊔ j) where
  no-eta-equality
  constructor _:&:_
  field
    proj₁ : A
    @0 proj₂ : P proj₁
open S0 public
infixr 4 _:&:_
{-# COMPILE AGDA2HS S0 newtype #-}
{-# FOREIGN AGDA2HS
infixr 4 :&:
#-}

-- Efficient CHAD representation of the Möbius LSTM cell.
--
-- Source semantics is real-valued Double. Q20 vectors are storage / policy
-- boundaries; the differentiated program is the continuous cell before
-- quantisation. The custom boundary derivative is straight-through only at
-- those explicit Q20 representation conversions.
--
-- Csimma-style agda2hs boundary: VecD is a Haskell unboxed Vector Double;
-- all runtime primitives have Agda postulate signatures and Haskell bodies
-- in FOREIGN AGDA2HS above. Sparse cotangents use Maybe, and parameter
-- accumulation uses local state-passing (LACM), rather than a tree of
-- higher-order derivative closures.
------------------------------------------------------------------------

dAbs : Double → Double
dAbs x = if dLess x dZero then dNegate x else x
{-# COMPILE AGDA2HS dAbs #-}

dSign : Double → Double
dSign x =
  if dLess x dZero then dNegate dOne
  else if dLess dZero x then dOne else dZero
{-# COMPILE AGDA2HS dSign #-}

dClip : Double → Double
dClip x =
  if dLess x (dNegate dOne) then dNegate dOne
  else if dLess dOne x then dOne else x
{-# COMPILE AGDA2HS dClip #-}

affineIdentityD : Double → Double
affineIdentityD x = x
{-# COMPILE AGDA2HS affineIdentityD #-}

-- This is the real-valued counterpart of shiftedSoftsignQ20:
-- (1 + z / (1 + |z|)) / 2. Its derivative is 1/(2(1+|z|)^2).
shiftedSoftsignD : Double → Double
shiftedSoftsignD z =
  dDiv (dAdd dOne (dDiv z (dAdd dOne (dAbs z)))) dTwo
{-# COMPILE AGDA2HS shiftedSoftsignD #-}

shiftedSoftsignD' : Double → Double
shiftedSoftsignD' z =
  let den = dAdd dOne (dAbs z)
  in dDiv dOne (dMul dTwo (dMul den den))
{-# COMPILE AGDA2HS shiftedSoftsignD' #-}

vDAdd : VecD → VecD → VecD
vDAdd x y = vDGen (vDLen x) (λ i → dAdd (vDAt x i) (vDAt y i))
{-# COMPILE AGDA2HS vDAdd #-}

vDZipMul : VecD → VecD → VecD
vDZipMul x y = vDGen (vDLen x) (λ i → dMul (vDAt x i) (vDAt y i))
{-# COMPILE AGDA2HS vDZipMul #-}

vDZero : Int64 → VecD
vDZero n = vDGen n (λ _ → dZero)
{-# COMPILE AGDA2HS vDZero #-}

vDSum : VecD → Double
vDSum = vDFoldlIdx (λ acc _ x → dAdd acc x) dZero
{-# COMPILE AGDA2HS vDSum #-}

vDDotRow : VecD → VecD → Int64 → Int64 → Double
vDDotRow weights input row lDim =
  vDFoldlIdx
    (λ acc i x →
      dAdd acc (dMul (vDAt weights (add64 (mul64 row lDim) i)) x))
    dZero input
{-# COMPILE AGDA2HS vDDotRow #-}

layerNormForwardD : VecD → (VecD × Double)
layerNormForwardD x =
  let n = i64ToDouble (vDLen x)
      mean = dDiv (vDSum x) n
      sqSum = vDFoldlIdx
        (λ acc _ value →
          let delta = dSub value mean
          in dAdd acc (dMul delta delta))
        dZero x
      variance = dDiv sqSum n
      invStd = dDiv dOne (dSqrt (dAdd variance dEpsilon))
      normalized = vDGen (vDLen x)
        (λ i → dMul (dSub (vDAt x i) mean) invStd)
  in normalized , invStd
{-# COMPILE AGDA2HS layerNormForwardD #-}

-- Reverse rule for layer normalisation:
-- dx = invStd * (dy - mean(dy) - y * mean(dy*y)).
layerNormPullbackD : Double → VecD → VecD → VecD
layerNormPullbackD invStd normalized dy =
  let n = i64ToDouble (vDLen dy)
      meanDy = dDiv (vDSum dy) n
      meanDyY = dDiv (vDSum (vDZipMul dy normalized)) n
  in vDGen (vDLen dy)
       (λ i →
         dMul invStd
           (dSub
             (dSub (vDAt dy i) meanDy)
             (dMul (vDAt normalized i) meanDyY)))
{-# COMPILE AGDA2HS layerNormPullbackD #-}

-- Reverse rule for clamp/signRelu: zero derivative outside (-1,1).
clipPullbackD : VecD → VecD → VecD
clipPullbackD normalized dy =
  vDGen (vDLen dy)
    (λ i →
      let x = vDAt normalized i
      in if dLess (dAbs x) dOne then vDAt dy i else dZero)
{-# COMPILE AGDA2HS clipPullbackD #-}

record MobiusLSTM3CacheD : Set where
  field
    cacheHDim cacheLDim : Int64
    cacheInputD cacheWfD cacheWiD cacheWoD cacheWgD : VecD
    cachePrevCellD cacheCellD : VecD
    cacheForgetPreD cacheInputPreD cacheOutputPreD : VecD
    cacheForgetD cacheInputGateD cacheCandidateD cacheOutputD : VecD
    cacheCellNumD cacheCellDenD : VecD
    cacheHiddenNormD : VecD
    cacheHiddenInvStdD : Double
{-# COMPILE AGDA2HS MobiusLSTM3CacheD #-}

open MobiusLSTM3CacheD public

record MobiusLSTM3Gradient : Set where
  field
    lstmDInput lstmDPrevCell : Maybe VecD
    lstmDWf lstmDWi lstmDWo lstmDWg : Maybe VecD
{-# COMPILE AGDA2HS MobiusLSTM3Gradient #-}

open MobiusLSTM3Gradient public

emptyMobiusLSTM3Gradient : MobiusLSTM3Gradient
emptyMobiusLSTM3Gradient =
  record
    { lstmDInput = Nothing
    ; lstmDPrevCell = Nothing
    ; lstmDWf = Nothing
    ; lstmDWi = Nothing
    ; lstmDWo = Nothing
    ; lstmDWg = Nothing
    }
{-# COMPILE AGDA2HS emptyMobiusLSTM3Gradient #-}

mobiusLSTM3ForwardD :
  Int64 → Vec64 → Vec64 → Vec64 → Vec64 → Vec64 → Vec64 →
  (Vec64 × Vec64) × MobiusLSTM3CacheD
mobiusLSTM3ForwardD hDim wf wi wo wg inLift cPrev =
  let x = vec64ToD inLift
      wfD = vec64ToD wf
      wiD = vec64ToD wi
      woD = vec64ToD wo
      wgD = vec64ToD wg
      cp = vec64ToD cPrev
      lDim = vDLen x
      forgetPre = vDGen hDim (λ h → vDDotRow wfD x h lDim)
      inputPre = vDGen hDim (λ h → vDDotRow wiD x h lDim)
      outputPre = vDGen hDim (λ h → vDDotRow woD x h lDim)
      candidatePre = vDGen hDim (λ h → vDDotRow wgD x h lDim)
      forgetGate = vDGen hDim (λ h → shiftedSoftsignD (vDAt forgetPre h))
      inputGate = vDGen hDim (λ h → shiftedSoftsignD (vDAt inputPre h))
      outputGate = vDGen hDim (λ h → shiftedSoftsignD (vDAt outputPre h))
      cellNum = vDGen hDim (λ h →
        dAdd
          (dMul (vDAt forgetGate h) (vDAt cp h))
          (dMul (vDAt inputGate h) (affineIdentityD (vDAt candidatePre h))))
      cellDen = vDGen hDim (λ h →
        dAdd dOne (dDiv (dAbs (vDAt cp h)) dEight))
      cellNew = vDGen hDim (λ h → dDiv (vDAt cellNum h) (vDAt cellDen h))
      hiddenRaw = vDGen hDim (λ h →
        dMul (vDAt outputGate h) (affineIdentityD (vDAt cellNew h)))
      (hiddenNorm , hiddenInvStd) = layerNormForwardD hiddenRaw
      hiddenClipped = vDGen hDim (λ h → dClip (vDAt hiddenNorm h))
      cache = record
        { cacheHDim = hDim
        ; cacheLDim = lDim
        ; cacheInputD = x
        ; cacheWfD = wfD
        ; cacheWiD = wiD
        ; cacheWoD = woD
        ; cacheWgD = wgD
        ; cachePrevCellD = cp
        ; cacheCellD = cellNew
        ; cacheForgetPreD = forgetPre
        ; cacheInputPreD = inputPre
        ; cacheOutputPreD = outputPre
        ; cacheForgetD = forgetGate
        ; cacheInputGateD = inputGate
        ; cacheCandidateD = candidatePre
        ; cacheOutputD = outputGate
        ; cacheCellNumD = cellNum
        ; cacheCellDenD = cellDen
        ; cacheHiddenNormD = hiddenNorm
        ; cacheHiddenInvStdD = hiddenInvStd
        }
  in ((vecDTo64 cellNew , vecDTo64 hiddenClipped) , cache)
{-# COMPILE AGDA2HS mobiusLSTM3ForwardD #-}

seedOrZeroD : Int64 → Maybe VecD → VecD
seedOrZeroD n Nothing = vDZero n
seedOrZeroD n (Just seed) = seed
{-# COMPILE AGDA2HS seedOrZeroD #-}

record MobiusLSTM3CHADResult : Set where
  field
    chadCellPrimal : Vec64
    chadHiddenPrimal : Vec64
    chadPullback : Maybe VecD → Maybe VecD → MobiusLSTM3Gradient
{-# COMPILE AGDA2HS MobiusLSTM3CHADResult #-}

open MobiusLSTM3CHADResult public

mobiusLSTM3VJP :
  MobiusLSTM3CacheD →
  Maybe VecD → Maybe VecD → MobiusLSTM3Gradient
mobiusLSTM3VJP cache Nothing Nothing = emptyMobiusLSTM3Gradient
mobiusLSTM3VJP cache cellSeed hiddenSeed =
  let hDim = cacheHDim cache
      lDim = cacheLDim cache
      dCellSeed = seedOrZeroD hDim cellSeed
      dHiddenSeed = seedOrZeroD hDim hiddenSeed
      dHiddenNorm = clipPullbackD (cacheHiddenNormD cache) dHiddenSeed
      dHiddenRaw = layerNormPullbackD (cacheHiddenInvStdD cache)
                    (cacheHiddenNormD cache) dHiddenNorm
      dCellFromHidden = vDZipMul dHiddenRaw (cacheOutputD cache)
      dCell = vDAdd dCellSeed dCellFromHidden
      dOutputGate = vDZipMul dHiddenRaw (cacheCellD cache)
      dOutputPre = vDGen hDim (λ h →
        dMul (vDAt dOutputGate h)
          (shiftedSoftsignD' (vDAt (cacheOutputPreD cache) h)))
      dCellNum = vDGen hDim (λ h →
        dDiv (vDAt dCell h) (vDAt (cacheCellDenD cache) h))
      dCellDen = vDGen hDim (λ h →
        dNegate
          (dDiv
            (dMul (vDAt dCell h) (vDAt (cacheCellNumD cache) h))
            (dMul (vDAt (cacheCellDenD cache) h) (vDAt (cacheCellDenD cache) h))))
      dPrevCell = vDGen hDim (λ h →
        dAdd
          (dMul (vDAt dCellNum h) (vDAt (cacheForgetD cache) h))
          (dMul (vDAt dCellDen h)
            (dDiv (dSign (vDAt (cachePrevCellD cache) h)) dEight)))
      dForgetPre = vDGen hDim (λ h →
        dMul
          (dMul (vDAt dCellNum h) (vDAt (cachePrevCellD cache) h))
          (shiftedSoftsignD' (vDAt (cacheForgetPreD cache) h)))
      dInputPre = vDGen hDim (λ h →
        dMul
          (dMul (vDAt dCellNum h) (vDAt (cacheCandidateD cache) h))
          (shiftedSoftsignD' (vDAt (cacheInputPreD cache) h)))
      -- Candidate gate is affine identity: derivative exactly one.
      dCandidatePre = vDGen hDim (λ h →
        dMul (vDAt dCellNum h) (vDAt (cacheInputGateD cache) h))
      dWf = vDGen (mul64 hDim lDim) (λ j →
        dMul (vDAt dForgetPre (quot64 j lDim))
             (vDAt (cacheInputD cache) (rem64 j lDim)))
      dWi = vDGen (mul64 hDim lDim) (λ j →
        dMul (vDAt dInputPre (quot64 j lDim))
             (vDAt (cacheInputD cache) (rem64 j lDim)))
      dWo = vDGen (mul64 hDim lDim) (λ j →
        dMul (vDAt dOutputPre (quot64 j lDim))
             (vDAt (cacheInputD cache) (rem64 j lDim)))
      dWg = vDGen (mul64 hDim lDim) (λ j →
        dMul (vDAt dCandidatePre (quot64 j lDim))
             (vDAt (cacheInputD cache) (rem64 j lDim)))
      dInput = vDGen lDim (λ i →
        vDFoldlIdx
          (λ acc h _ →
            let row = add64 (mul64 h lDim) i
                df = dMul (vDAt dForgetPre h) (vDAt (cacheWfD cache) row)
                di = dMul (vDAt dInputPre h) (vDAt (cacheWiD cache) row)
                dOut = dMul (vDAt dOutputPre h) (vDAt (cacheWoD cache) row)
                dg = dMul (vDAt dCandidatePre h) (vDAt (cacheWgD cache) row)
            in dAdd acc (dAdd df (dAdd di (dAdd dOut dg))))
          dZero dForgetPre)
  in record
    { lstmDInput = Just dInput
    ; lstmDPrevCell = Just dPrevCell
    ; lstmDWf = Just dWf
    ; lstmDWi = Just dWi
    ; lstmDWo = Just dWo
    ; lstmDWg = Just dWg
    }
{-# COMPILE AGDA2HS mobiusLSTM3VJP #-}

mobiusLSTM3CHAD :
  Int64 → Vec64 → Vec64 → Vec64 → Vec64 → Vec64 → Vec64 →
  MobiusLSTM3CHADResult
mobiusLSTM3CHAD hDim wf wi wo wg inLift cPrev =
  let ((cellPrimal , hiddenPrimal) , cache) =
        mobiusLSTM3ForwardD hDim wf wi wo wg inLift cPrev
  in record
    { chadCellPrimal = cellPrimal
    ; chadHiddenPrimal = hiddenPrimal
    ; chadPullback = mobiusLSTM3VJP cache
    }
{-# COMPILE AGDA2HS mobiusLSTM3CHAD #-}

-- A state-passing local accumulation monad. Maybe VecD is the sparse
-- cotangent carrier: Nothing means this output contributes no update.
LACM : Set → Set → Set
LACM S A = S → A × S

pureLACM : {S A : Set} → A → LACM S A
pureLACM x state = x , state
{-# COMPILE AGDA2HS pureLACM #-}

bindLACM :
  {S A B : Set} →
  LACM S A → (A → LACM S B) → LACM S B
bindLACM first next state =
  let (value , state') = first state
  in next value state'
{-# COMPILE AGDA2HS bindLACM #-}

mergeMaybeVecD : Maybe VecD → Maybe VecD → Maybe VecD
mergeMaybeVecD Nothing right = right
mergeMaybeVecD left Nothing = left
mergeMaybeVecD (Just left) (Just right) = Just (vDAdd left right)
{-# COMPILE AGDA2HS mergeMaybeVecD #-}

mergeMobiusLSTM3Gradient :
  MobiusLSTM3Gradient → MobiusLSTM3Gradient → MobiusLSTM3Gradient
mergeMobiusLSTM3Gradient left right =
  record
    { lstmDInput = mergeMaybeVecD (lstmDInput left) (lstmDInput right)
    ; lstmDPrevCell = mergeMaybeVecD (lstmDPrevCell left) (lstmDPrevCell right)
    ; lstmDWf = mergeMaybeVecD (lstmDWf left) (lstmDWf right)
    ; lstmDWi = mergeMaybeVecD (lstmDWi left) (lstmDWi right)
    ; lstmDWo = mergeMaybeVecD (lstmDWo left) (lstmDWo right)
    ; lstmDWg = mergeMaybeVecD (lstmDWg left) (lstmDWg right)
    }
{-# COMPILE AGDA2HS mergeMobiusLSTM3Gradient #-}

accumulateMobiusLSTM3Gradient :
  MobiusLSTM3Gradient → LACM MobiusLSTM3Gradient ⊤
accumulateMobiusLSTM3Gradient gradient =
  bindLACM (pureLACM tt)
    (λ _ state → tt , mergeMobiusLSTM3Gradient state gradient)
{-# COMPILE AGDA2HS accumulateMobiusLSTM3Gradient #-}

applyMobiusLSTM3Accumulator :
  MobiusLSTM3Gradient → MobiusLSTM3Gradient → MobiusLSTM3Gradient
applyMobiusLSTM3Accumulator initial gradient =
  snd (accumulateMobiusLSTM3Gradient gradient initial)
{-# COMPILE AGDA2HS applyMobiusLSTM3Accumulator #-}

updateQ20FromDoubleGradient :
  Int64 → Vec64 → Maybe VecD → Vec64
updateQ20FromDoubleGradient rate weights Nothing = weights
updateQ20FromDoubleGradient rate weights (Just gradient) =
  vGen64 (vLen64 weights) (λ i →
    add64 (vAt64 weights i)
      (splitMulQ20 rate (doubleToQ20 (vDAt gradient i))))
{-# COMPILE AGDA2HS updateQ20FromDoubleGradient #-}

-- The original public step now executes the CHAD-transformed cell's primal.
mobiusLSTM3Step :
  Int64 → Vec64 → Vec64 → Vec64 → Vec64 → Vec64 → Vec64 →
  (Vec64 × Vec64)
mobiusLSTM3Step hDim wf wi wo wg inLift cPrev =
  let chad = mobiusLSTM3CHAD hDim wf wi wo wg inLift cPrev
  in (chadCellPrimal chad , chadHiddenPrimal chad)
{-# COMPILE AGDA2HS mobiusLSTM3Step #-}

-- Csimma S0 packages executable representation with its erased primal
-- simulation proof. Pullback closure remains part of the runtime value.
mobiusLSTM3CHADCertified :
  (hDim : Int64) →
  (wf wi wo wg inLift cPrev : Vec64) →
  S0 MobiusLSTM3CHADResult
    (λ result →
      mobiusLSTM3Step hDim wf wi wo wg inLift cPrev ≡
      (chadCellPrimal result , chadHiddenPrimal result))
mobiusLSTM3CHADCertified hDim wf wi wo wg inLift cPrev =
  let result = mobiusLSTM3CHAD hDim wf wi wo wg inLift cPrev
  in result :&: refl
{-# COMPILE AGDA2HS mobiusLSTM3CHADCertified #-}
------------------------------------------------------------------------
-- 1-Step Clamped Bishop-Wildberger RationalHL + StreamingOptimizer
------------------------------------------------------------------------

pcgStep64 : Int64 → (Int64 × Int64)
pcgStep64 st =
  let st' = add64 (mul64 st (lit64 6364136223846793005)) (lit64 1442695040888963407)
      r   = and64 (shiftR64 st' (lit64 43)) qMask20
  in (st' , r)
{-# COMPILE AGDA2HS pcgStep64 #-}

binCenterQ20 : Int64 → Int64
binCenterQ20 k = shiftL64 (sub64 (mul64 (lit64 6) k) (lit64 2)) qShift64
{-# COMPILE AGDA2HS binCenterQ20 #-}

record CraftaxRHLLSTMState : Set where
  field
    hDim      : Int64
    fDim      : Int64
    nAct      : Int64
    nBins     : Int64
    stepTick  : Int64
    wf        : Vec64
    wi        : Vec64
    wo        : Vec64
    wg        : Vec64
    cCell     : Vec64
    qWeights  : Vec64   -- nAct * nBins * fDim (Strict 0-Init)
    qVMax     : Vec64
    qL2Rem    : Vec64
    lastSeen  : Vec64
    prngState : Int64
open CraftaxRHLLSTMState public
{-# COMPILE AGDA2HS CraftaxRHLLSTMState #-}

initCraftaxRHLLSTM : Int64 → CraftaxRHLLSTMState
initCraftaxRHLLSTM seed =
  let hd    = lit64 8
      ld    = lit64 64
      fd    = lit64 72
      na    = lit64 17
      nb    = lit64 5
      rsc   = shiftR64 qOne64 (lit64 4)
      genR  = λ off → vGen64 (mul64 hd ld) (λ i →
                let (_ , r) = pcgStep64 (add64 seed (add64 off i))
                in if eq64 (and64 r (lit64 1)) (lit64 0) then rsc else sub64 (lit64 0) rsc)
      zeros = λ m → vGen64 m (λ _ → lit64 0)
      tot   = mul64 (mul64 na nb) fd
  in record
       { hDim      = hd
       ; fDim      = fd
       ; nAct      = na
       ; nBins     = nb
       ; stepTick  = lit64 0
       ; wf        = genR (lit64 1009)
       ; wi        = genR (lit64 2027)
       ; wo        = genR (lit64 3049)
       ; wg        = genR (lit64 4099)
       ; cCell     = zeros hd
       ; qWeights  = zeros tot
       ; qVMax     = zeros tot
       ; qL2Rem    = zeros tot
       ; lastSeen  = zeros na
       ; prngState = add64 seed (lit64 1)
       }
{-# COMPILE AGDA2HS initCraftaxRHLLSTM #-}

encodeLSTMFeatures : CraftaxRHLLSTMState → Vec64 → Vec64 → (Vec64 × Vec64)
encodeLSTMFeatures s obs32 cPrev =
  let inLift = whtAtrousConcat64 obs32
      chad = proj₁ (mobiusLSTM3CHADCertified
        (hDim s) (wf s) (wi s) (wo s) (wg s) inLift cPrev)
  in (vAppend64 inLift (chadHiddenPrimal chad) , chadCellPrimal chad)
{-# COMPILE AGDA2HS encodeLSTMFeatures #-}

evalActionRationalHL : CraftaxRHLLSTMState → Vec64 → Int64 → (Vec64 × Int64)
evalActionRationalHL s feat a =
  let fd     = fDim s
      nb     = nBins s
      qw     = qWeights s
      baseA  = mul64 a (mul64 nb fd)
      logits = vGen64 nb (λ k →
                 let baseK = add64 baseA (mul64 k fd)
                 in vFoldlIdx64 (λ acc i f → add64 acc (splitMulQ20 (vAt64 qw (add64 baseK i)) f)) (lit64 0) feat)
      zmax   = vFoldlIdx64 (λ mx _ z → max64 mx z) (vAt64 logits (lit64 0)) logits
      rawP   = vMap64 (λ z →
                 let d = sub64 zmax z
                 in mulRecipPade1 qOne64 (add64 qOne64 (add64 d (shiftR64 (splitMulQ20 d d) (lit64 1))))) logits
      pSum   = vFoldlIdx64 (λ acc _ p → add64 acc p) (lit64 0) rawP
      probs  = vMap64 (λ p → mulRecipPade1 p pSum) rawP
      meanV  = vFoldlIdx64 (λ acc k p → add64 acc (splitMulQ20 p (binCenterQ20 k))) (lit64 0) probs
  in (probs , meanV)
{-# COMPILE AGDA2HS evalActionRationalHL #-}

selectActionEpsGreedy : CraftaxRHLLSTMState → Vec64 → (Int64 × Int64)
selectActionEpsGreedy s feat =
  let na        = nAct s
      (st' , r) = pcgStep64 (prngState s)
      qs        = vGen64 na (λ a → snd (evalActionRationalHL s feat a))
      bestA     = vFoldlIdx64 (λ ba i q → if gt64 q (vAt64 qs ba) then i else ba) (lit64 0) qs
      epsAct    = and64 r (lit64 15)
  in if eq64 epsAct (lit64 0)
     then let (st'' , r2) = pcgStep64 st'
              rndA        = vFoldlIdx64 (λ acc i _ → if ge64 (mul64 r2 na) (mul64 i qOne64) then i else acc) (lit64 0) qs
          in (rndA , st'')
     else (bestA , st')
{-# COMPILE AGDA2HS selectActionEpsGreedy #-}

tentProject5 : Int64 → Vec64
tentProject5 targ =
  let tc   = clamp64 targ (binCenterQ20 (lit64 0)) (binCenterQ20 (lit64 4))
      invW = lit64 174763 -- 1/6 in Q20
      rawT = vGen64 (lit64 5) (λ k → relu64 (sub64 qOne64 (splitMulQ20 (abs64 (sub64 tc (binCenterQ20 k))) invW)))
      tSum = vFoldlIdx64 (λ acc _ v → add64 acc v) (lit64 0) rawT
  in vMap64 (λ v → mulRecipPade1 v tSum) rawT
{-# COMPILE AGDA2HS tentProject5 #-}

craftaxRHLLSTMStep : CraftaxRHLLSTMState → Vec64 → Int64 → Int64 → Vec64 → Bool → CraftaxRHLLSTMState
craftaxRHLLSTMStep s obsCur actTaken rewQ obsNxt isDone =
  let tick = add64 (stepTick s) (lit64 1)
      -- Keep the actual CHAD pullback produced by this very forward pass.
      inLiftCur = whtAtrousConcat64 obsCur
      rnnCur = proj₁ (mobiusLSTM3CHADCertified
        (hDim s) (wf s) (wi s) (wo s) (wg s) inLiftCur (cCell s))
      featCur = vAppend64 inLiftCur (chadHiddenPrimal rnnCur)
      cNxt0 = chadCellPrimal rnnCur
      cNxt = if isDone then vMap64 (λ _ → lit64 0) cNxt0 else cNxt0
      (featNxt , _)     = encodeLSTMFeatures s obsNxt cNxt
      na                = nAct s
      nb                = nBins s
      fd                = fDim s
      dt                = sub64 tick (vAt64 (lastSeen s) actTaken)
      (pCur , _)        = evalActionRationalHL s featCur actTaken
      qsNxt             = vGen64 na (λ a → snd (evalActionRationalHL s featNxt a))
      bestNxt           = vFoldlIdx64 (λ ba i q → if gt64 q (vAt64 qsNxt ba) then i else ba) (lit64 0) qsNxt
      vBoot             = if isDone then lit64 0 else splitMulQ20 gammaQ64 (vAt64 qsNxt bestNxt)
      tProbs            = tentProject5 (add64 rewQ vBoot)
      gBins             = vGen64 nb (λ k → sub64 (vAt64 tProbs k) (vAt64 pCur k))
      loAct             = mul64 actTaken (mul64 nb fd)
      hiAct             = add64 loAct (mul64 nb fd)
      qw                = qWeights s
      -- Policy cotangent for hidden coordinates. Q20 conversion is the
      -- explicit boundary between the quantised policy head and the real
      -- valued CHAD recurrence.
      hiddenOffset = vLen64 inLiftCur
      -- Differentiate the normalized rational score used by
      -- evalActionRationalHL, not an assumed softmax. For
      -- r(d)=1/(1+d+d²/2), dlog(r)/dlogit=(1+d)/(1+d+d²/2).
      policyLogits = vGen64 nb (λ k →
        let baseK = add64 loAct (mul64 k fd)
        in vFoldlIdx64
             (λ acc i feature →
               add64 acc (splitMulQ20
                 (vAt64 qw (add64 baseK i)) feature))
             (lit64 0) featCur)
      policyMax = vFoldlIdx64
        (λ mx _ z → max64 mx z)
        (vAt64 policyLogits (lit64 0)) policyLogits
      dHiddenSeed = vDGen (hDim s) (λ h →
        q20ToDouble
          (vFoldlIdx64
            (λ acc k _ →
              let delta = sub64 policyMax (vAt64 policyLogits k)
                  denom = add64 qOne64
                    (add64 delta
                      (shiftR64 (splitMulQ20 delta delta) (lit64 1)))
                  logScoreSlope =
                    mulRecipPade1 (add64 qOne64 delta) denom
                  scoreCotangent =
                    splitMulQ20 (vAt64 gBins k) logScoreSlope
                  weightIndex = add64 loAct
                    (add64 (mul64 k fd) (add64 hiddenOffset h))
              in add64 acc
                   (splitMulQ20 (vAt64 qw weightIndex) scoreCotangent))
            (lit64 0) gBins))
      rnnGradientRaw = chadPullback rnnCur Nothing (Just dHiddenSeed)
      -- LACM-style state passing merges sparse cotangent products. The
      -- previous-cell cotangent remains available for callers unrolling a
      -- longer sequence; this online learner currently truncates BPTT here.
      rnnGradient =
        applyMobiusLSTM3Accumulator emptyMobiusLSTM3Gradient rnnGradientRaw
      wf' = updateQ20FromDoubleGradient lrBase64 (wf s) (lstmDWf rnnGradient)
      wi' = updateQ20FromDoubleGradient lrBase64 (wi s) (lstmDWi rnnGradient)
      wo' = updateQ20FromDoubleGradient lrBase64 (wo s) (lstmDWo rnnGradient)
      wg' = updateQ20FromDoubleGradient lrBase64 (wg s) (lstmDWg rnnGradient)
      qv                = qVMax s
      qr                = qL2Rem s
      totN              = mul64 (mul64 na nb) fd
      binIdx            = λ m → vFoldlIdx64 (λ acc bk _ → if ge64 m (mul64 bk fd) then bk else acc) (lit64 0) gBins
      updV              = vGen64 (mul64 nb fd) (λ m →
                            let k   = binIdx m
                                i   = sub64 m (mul64 k fd)
                                idx = add64 loAct m
                                ui  = splitMulQ20 (vAt64 gBins k) (vAt64 featCur i)
                            in max64
                                  (splitMulQ20
                                    (powQ20Loop qOne64 betaStream64 dt)
                                    (vAt64 qv idx))
                                  (abs64 ui))
      l2Weights = vGen64 totN (λ j →
                     if ge64 j loAct then
                       if lt64 j hiAct then
                         fst (decayL2Catchup dt (vAt64 qw j) (vAt64 qr j) qOne64)
                       else vAt64 qw j
                     else vAt64 qw j)
      l2Residuals = vGen64 totN (λ j →
                       if ge64 j loAct then
                         if lt64 j hiAct then
                           snd (decayL2Catchup dt (vAt64 qw j) (vAt64 qr j) qOne64)
                         else vAt64 qr j
                       else vAt64 qr j)
      gradStep = λ m →
                   let k      = binIdx m
                       i      = sub64 m (mul64 k fd)
                       signal = splitMulQ20 (vAt64 gBins k) (vAt64 featCur i)
                       denom  = max64 (vAt64 updV m) (lit64 1)
                       unit   = clamp64 (mulRecipPade1 signal denom)
                                 (sub64 (lit64 0) qOne64) qOne64
                   in splitMulQ20 lrBase64 unit
      qw' = vGen64 totN (λ j →
              if ge64 j loAct then
                if lt64 j hiAct then
                  add64 (vAt64 l2Weights j) (gradStep (sub64 j loAct))
                else vAt64 qw j
              else vAt64 qw j)
      qv' = vGen64 totN (λ j →
              if ge64 j loAct then
                if lt64 j hiAct then
                  vAt64 updV (sub64 j loAct)
                else vAt64 qv j
              else vAt64 qv j)
      qr' = l2Residuals
      seen' = vGen64 na (λ a →
                if eq64 a actTaken then tick else vAt64 (lastSeen s) a)
  in record
       { hDim      = hDim s
       ; fDim      = fDim s
       ; nAct      = nAct s
       ; nBins     = nBins s
       ; stepTick  = tick
       ; wf        = wf'
       ; wi        = wi'
       ; wo        = wo'
       ; wg        = wg'
       ; cCell     = cNxt
       ; qWeights  = qw'
       ; qVMax     = qv'
       ; qL2Rem    = qr'
       ; lastSeen  = seen'
       ; prngState = prngState s
       }
{-# COMPILE AGDA2HS craftaxRHLLSTMStep #-}
