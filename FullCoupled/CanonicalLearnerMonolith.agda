{-# OPTIONS
--experimental-lazy-instances
--safe
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
-- Keep imported generic binders out of scope so the canonical module's
-- explicit variable block owns its identifiers without namespace clashes.
--
-- Csimma's agda2hs/C++ methodology uses Haskell.Prelude plus narrow
-- postulate/FOREIGN AGDA2HS adapters for external Haskell dependencies.
-- This learner has no IORef, pointer, StablePtr, or CFuture boundary, so
-- those FFI-specific toolkit imports do not belong in this pure module.
--
-- Reflection is an Agda type-checker API. It is available to Agda macros;
-- agda2hs does not translate the macro implementation into Haskell.
-- Keep it Agda-side and do not mark reflection declarations COMPILE AGDA2HS.
--
-- Agda's builtin rewrite rules require --rewriting. That option is
-- incompatible with this module's --safe trust boundary, so the
-- Agda.Builtin.Equality.Rewrite module is intentionally not imported here.

-- Required for Polymorphism:
open import Agda.Primitive using (Level; lsuc; _⊔_) public
open import Haskell.Prim public
open import Haskell.Prelude public
open import Haskell.Laws public
open import Haskell.Prim.Thunk public
import Agda.Builtin.Reflection
import Agda.Builtin.Erased.Erased
open import Agda.Builtin.Erased.Funext public
open import Agda.Builtin.Erased.Propext public
open import Agda.Builtin.Erased.Quotient public

{-# FOREIGN AGDA2HS
{-# LANGUAGE BangPatterns #-}
import qualified Data.Bits as Bits
import Data.Int (Int64)
import Data.Word (Word64)
import Data.Vector.Unboxed (Vector)
import qualified Data.Vector.Unboxed as VU
import Control.Parallel.Strategies (parMap, rdeepseq)

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

parSeeds :: (Int64 -> Int64) -> [Int64] -> [Int64]
parSeeds = parMap rdeepseq
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
  parSeeds    : (Int64 → Int64) → List Int64 → List Int64

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

softsignQ20 : Int64 → Int64
softsignQ20 z = mulRecipPade1 z (add64 qOne64 (abs64 z))
{-# COMPILE AGDA2HS softsignQ20 #-}

whtAtrousConcat64 : Vec64 → Vec64
whtAtrousConcat64 obs32 =
  let b1 = signReluVec (intLayerNormPow2 (lit64 5) (whtButterfly32 obs32))
      b2 = signReluVec (intLayerNormPow2 (lit64 5) (atrousHaar32 obs32))
  in vAppend64 b1 b2
{-# COMPILE AGDA2HS whtAtrousConcat64 #-}

mobiusLSTM3Step : Int64 → Vec64 → Vec64 → Vec64 → Vec64 → Vec64 → Vec64 → (Vec64 × Vec64)
mobiusLSTM3Step hDim wf wi wo wg inLift cPrev =
  let lDim = vLen64 inLift
      dotR = λ w base → vFoldlIdx64 (λ acc i x → add64 acc (splitMulQ20 (vAt64 w (add64 base i)) x)) (lit64 0) inLift
      cNew = vGen64 hDim (λ h →
               let base = mul64 h lDim
                   ft   = shiftedSoftsignQ20 (dotR wf base)
                   it   = shiftedSoftsignQ20 (dotR wi base)
                   g    = softsignQ20 (dotR wg base)
                   cp   = vAt64 cPrev h
                   num  = add64 (splitMulQ20 ft cp) (splitMulQ20 it g)
                   den  = add64 qOne64 (shiftR64 (abs64 cp) (lit64 3))
               in mulRecipPade1 num den)
      hNew = vGen64 hDim (λ h →
               let base = mul64 h lDim
                   ot   = shiftedSoftsignQ20 (dotR wo base)
               in splitMulQ20 ot (softsignQ20 (vAt64 cNew h)))
  in (cNew , hNew)
{-# COMPILE AGDA2HS mobiusLSTM3Step #-}

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
  let inLift        = whtAtrousConcat64 obs32
      (cNew , hNew) = mobiusLSTM3Step (hDim s) (wf s) (wi s) (wo s) (wg s) inLift cPrev
      hLift         = signReluVec (intLayerNormPow2 (lit64 3) hNew)
  in (vAppend64 inLift hLift , cNew)
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
  let tick              = add64 (stepTick s) (lit64 1)
      (featCur , cNxt0) = encodeLSTMFeatures s obsCur (cCell s)
      cNxt              = if isDone then vMap64 (λ _ → lit64 0) cNxt0 else cNxt0
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
       ; wf        = wf s
       ; wi        = wi s
       ; wo        = wo s
       ; wg        = wg s
       ; cCell     = cNxt
       ; qWeights  = qw'
       ; qVMax     = qv'
       ; qL2Rem    = qr'
       ; lastSeen  = seen'
       ; prngState = prngState s
       }
{-# COMPILE AGDA2HS craftaxRHLLSTMStep #-}