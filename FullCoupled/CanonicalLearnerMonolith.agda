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
-- Canonical integer-only Q12.20 learner semantics.
------------------------------------------------------------------------

module FullCoupled.CanonicalLearnerMonolith where

-- Merged external import surface; internal FullCoupled imports remain module-local.
-- The agda2hs base library provides the Haskell-facing Prelude,
-- including Haskell.Prim's core types, equality, and Double.
-- Numeric/vector kernels use Csimma's postulate
  Int32 Vec32 : Set
  lit32 : Integer → Int32
  add32 sub32 mul32 shiftL32 shiftR32 and32 xor32 : Int32 → Int32 → Int32
  clz32 : Int32 → Int32
  eq32 gt32 lt32 ge32 le32 : Int32 → Int32 → Bool
  qAdd32 qSub32 qMul20 qDiv20 qSqrt20 : Int32 → Int32 → Int32
  vLen32 : Vec32 → Int32
  vAt32 : Vec32 → Int32 → Int32
  vGen32 : Int32 → (Int32 → Int32) → Vec32
  vMap32 : (Int32 → Int32) → Vec32 → Vec32
  vAppend32 : Vec32 → Vec32 → Vec32
  vFoldlIdx32 : (Int32 → Int32 → Int32 → Int32) → Int32 → Vec32 → Int32

------------------------------------------------------------------------
-- Exact Q12.20 dyadic constants: Int32 storage, Int64 widened products only.
------------------------------------------------------------------------

qShift32 qOne32 qHalf32 qMask20 lrBase64 betaStream32 gammaQ32 : Int32
qShift32     = lit32 20
qOne32       = lit32 1048576
qHalf32      = lit32 524288
qMask20      = lit32 1048575
lrBase64     = lit32 65536      -- 1/16
betaStream32 = lit32 1048524    -- 0.99995
gammaQ32     = lit32 1048524    -- 0.99995
{-# COMPILE AGDA2HS qShift32 #-}
{-# COMPILE AGDA2HS qHalf32 #-}
{-# COMPILE AGDA2HS qOne32 #-}
{-# COMPILE AGDA2HS qMask20 #-}
{-# COMPILE AGDA2HS lrBase64 #-}
{-# COMPILE AGDA2HS betaStream32 #-}
{-# COMPILE AGDA2HS gammaQ32 #-}

------------------------------------------------------------------------
-- Q12.20 ALU + bounded Padé-Newton reciprocal
------------------------------------------------------------------------

abs32 : Int32 → Int32
abs32 x = let m = shiftR32 x (lit32 31) in sub32 (xor32 x m) m
{-# COMPILE AGDA2HS abs32 #-}

sign32 : Int32 → Int32
sign32 x =
  sub32 (if gt32 x (lit32 0) then lit32 1 else lit32 0)
        (if lt32 x (lit32 0) then lit32 1 else lit32 0)
{-# COMPILE AGDA2HS sign32 #-}

max32 : Int32 → Int32 → Int32
max32 a b = let d = sub32 a b in sub32 a (and32 d (shiftR32 d (lit32 63)))
{-# COMPILE AGDA2HS max32 #-}

min32 : Int32 → Int32 → Int32
min32 a b = let d = sub32 a b in add32 b (and32 d (shiftR32 d (lit32 63)))
{-# COMPILE AGDA2HS min32 #-}

clamp32 : Int32 → Int32 → Int32 → Int32
clamp32 x lo hi = min32 (max32 x lo) hi
{-# COMPILE AGDA2HS clamp32 #-}

relu32 : Int32 → Int32
relu32 x = max32 x (lit32 0)
{-# COMPILE AGDA2HS relu32 #-}

splitMulQ20 : Int32 → Int32 → Int32
splitMulQ20 = qMul20
{-# COMPILE AGDA2HS splitMulQ20 #-}

padeMid4 padeC04 padeC14 : Int32 → Int32
padeMid4 b =
  if eq32 b (lit32 0) then lit32 1179648
  else if eq32 b (lit32 1) then lit32 1441792
  else if eq32 b (lit32 2) then lit32 1703936
  else lit32 1966080
padeC04 b =
  if eq32 b (lit32 0) then lit32 932068
  else if eq32 b (lit32 1) then lit32 762601
  else if eq32 b (lit32 2) then lit32 645278
  else lit32 559241
padeC14 b =
  if eq32 b (lit32 0) then lit32 828505
  else if eq32 b (lit32 1) then lit32 554619
  else if eq32 b (lit32 2) then lit32 397094
  else lit32 298262
{-# COMPILE AGDA2HS padeMid4 #-}
{-# COMPILE AGDA2HS padeC04 #-}
{-# COMPILE AGDA2HS padeC14 #-}

mulRecipPade1 : Int32 → Int32 → Int32
mulRecipPade1 x d =
  if eq32 d (lit32 0) then lit32 0
  else
    let s    = mul32 (sign32 x) (sign32 d)
        ax   = abs32 x
        ad   = abs32 d
        b    = sub32 (lit32 31) (clz32 ad)
        sh   = sub32 b qShift32
        m    = if ge32 sh (lit32 0) then shiftR32 ad sh else shiftL32 ad (sub32 (lit32 0) sh)
        bin  = and32 (shiftR32 (sub32 m qOne32) (lit32 18)) (lit32 3)
        t    = sub32 m (padeMid4 bin)
        y0   = sub32 (padeC04 bin) (splitMulQ20 (padeC14 bin) t)
        two  = shiftL32 (lit32 2) (lit32 20)
        y1   = splitMulQ20 y0 (sub32 two (splitMulQ20 m y0))
        prod = splitMulQ20 ax y1
    in mul32 s (if ge32 sh (lit32 0) then shiftR32 prod sh else shiftL32 prod (sub32 (lit32 0) sh))
{-# COMPILE AGDA2HS mulRecipPade1 #-}

invSqrtQ20 : Int32 → Int32
invSqrtQ20 v =
  if le32 v (lit32 0) then qOne32
  else
    let b   = sub32 (lit32 31) (clz32 v)
        e   = sub32 b qShift32
        h   = if ge32 e (lit32 0) then shiftR32 e (lit32 1)
              else sub32 (lit32 0) (shiftR32 (add32 (sub32 (lit32 0) e) (lit32 1)) (lit32 1))
        sh  = mul32 (lit32 2) h
        m   = if ge32 sh (lit32 0) then shiftR32 v sh else shiftL32 v (sub32 (lit32 0) sh)
        ms  = if le32 m (lit32 0) then qOne32 else m
        t   = sub32 ms (shiftL32 (lit32 2) (lit32 20))
        y0  = add32 (sub32 (lit32 741455) (splitMulQ20 (lit32 185364) t))
                    (splitMulQ20 (lit32 66200) (splitMulQ20 t t))
        ys  = if lt32 y0 (shiftL32 (lit32 1) (lit32 17)) then shiftL32 (lit32 1) (lit32 18) else y0
        thr = shiftL32 (lit32 3) (lit32 20)
        stp = λ y → shiftR32 (splitMulQ20 y (sub32 thr (splitMulQ20 ms (splitMulQ20 y y)))) (lit32 1)
        y2  = stp (stp ys)
    in if ge32 h (lit32 0) then shiftR32 y2 h else shiftL32 y2 (sub32 (lit32 0) h)
{-# COMPILE AGDA2HS invSqrtQ20 #-}

-- Exact O(log dt) Lazy Per-Action L2 = 2^-16 Catchup w/ Consistent Residue.
-- Int32 exponents are nonnegative signed 64-bit values at this call site.
-- A fixed 64-step structural fuel bound makes the bit loop total in Agda;
-- every positive Int32 reaches zero after at most 63 arithmetic right shifts.
powQ20LoopFuel : Nat → Int32 → Int32 → Int32 → Int32
powQ20LoopFuel zero acc base e = acc
powQ20LoopFuel (suc fuel) acc base e =
  if le32 e (lit32 0) then acc
  else
    let acc'  = if eq32 (and32 e (lit32 1)) (lit32 1) then splitMulQ20 acc base else acc
        base' = splitMulQ20 base base
    in powQ20LoopFuel fuel acc' base' (shiftR32 e (lit32 1))
{-# COMPILE AGDA2HS powQ20LoopFuel #-}

powQ20Loop : Int32 → Int32 → Int32 → Int32
powQ20Loop acc base e = powQ20LoopFuel 32 acc base e
{-# COMPILE AGDA2HS powQ20Loop #-}

decayL2Catchup : Int32 → Int32 → Int32 → Int32 → (Int32 × Int32)
decayL2Catchup dt w rem lr =
  if le32 dt (lit32 0) then (w , rem)
  else if eq32 dt (lit32 1) then
    let tot  = add32 (splitMulQ20 lr w) rem
        smag = shiftR32 (abs32 tot) (lit32 16)
        step = mul32 (sign32 tot) smag
        rem' = sub32 tot (shiftL32 step (lit32 16))
    in (sub32 w step , rem')
  else
    let stepQ = shiftR32 lr (lit32 16)
        baseQ = sub32 qOne32 stepQ
        effD  = sub32 qOne32 (powQ20Loop qOne32 baseQ dt)
        tot   = add32 (shiftL32 (splitMulQ20 effD w) (lit32 16)) rem
        step  = mul32 (sign32 tot) (shiftR32 (abs32 tot) (lit32 16))
        rem'  = sub32 tot (shiftL32 step (lit32 16))
    in (sub32 w step , rem')
{-# COMPILE AGDA2HS decayL2Catchup #-}

------------------------------------------------------------------------
-- WHT Butterfly + À Trous Haar + LayerNorm + Identity-candidate convex-gate GRU
------------------------------------------------------------------------

whtStep32 : Int32 → Vec32 → Vec32
whtStep32 len v =
  vGen32 (lit32 32) (λ i →
    let inHi    = gt32 (and32 i len) (lit32 0)
        partner = xor32 i len
        a       = vAt32 v (if inHi then partner else i)
        b       = vAt32 v (if inHi then i else partner)
    in if inHi then sub32 a b else add32 a b)
{-# COMPILE AGDA2HS whtStep32 #-}

whtButterfly32 : Vec32 → Vec32
whtButterfly32 v0 =
  let v16 = whtStep32 (lit32 16) (whtStep32 (lit32 8) (whtStep32 (lit32 4) (whtStep32 (lit32 2) (whtStep32 (lit32 1) v0))))
  in vMap32 (λ x → shiftR32 x (lit32 3)) v16
{-# COMPILE AGDA2HS whtButterfly32 #-}

atrousPass32 : Int32 → Vec32 → Vec32
atrousPass32 s v =
  vGen32 (lit32 32) (λ i →
    let j = and32 (add32 i s) (lit32 31)
        a = vAt32 v i
        b = vAt32 v j
    in if eq32 (and32 i (lit32 1)) (lit32 0) then shiftR32 (add32 a b) (lit32 1) else shiftR32 (sub32 a b) (lit32 1))
{-# COMPILE AGDA2HS atrousPass32 #-}

atrousHaar32 : Vec32 → Vec32
atrousHaar32 v0 = atrousPass32 (lit32 4) (atrousPass32 (lit32 2) (atrousPass32 (lit32 1) v0))
{-# COMPILE AGDA2HS atrousHaar32 #-}

intLayerNormPow2 : Int32 → Vec32 → Vec32
intLayerNormPow2 sh v =
  let sumV   = vFoldlIdx32 (λ acc _ x → add32 acc x) (lit32 0) v
      meanV  = shiftR32 sumV sh
      varSum = vFoldlIdx32 (λ acc _ x → let d = sub32 x meanV in add32 acc (splitMulQ20 d d)) (lit32 0) v
      invStd = invSqrtQ20 (add32 (shiftR32 varSum sh) (lit32 1024))
  in vMap32 (λ x → splitMulQ20 (sub32 x meanV) invStd) v
{-# COMPILE AGDA2HS intLayerNormPow2 #-}

signReluVec : Vec32 → Vec32
signReluVec = vMap32 (λ x → mul32 (sign32 x) (min32 (abs32 x) qOne32))
{-# COMPILE AGDA2HS signReluVec #-}

shiftedSoftsignQ20 : Int32 → Int32
shiftedSoftsignQ20 z = shiftR32 (add32 qOne32 (mulRecipPade1 z (add32 qOne32 (abs32 z)))) (lit32 1)
{-# COMPILE AGDA2HS shiftedSoftsignQ20 #-}

-- Identity activation for candidate/output paths. Shifted gate transfer
-- functions remain unchanged.
affineIdentityQ20 : Int32 → Int32
affineIdentityQ20 z = z
{-# COMPILE AGDA2HS affineIdentityQ20 #-}

whtAtrousConcat64 : Vec32 → Vec32
whtAtrousConcat64 obs32 =
  let b1 = signReluVec (intLayerNormPow2 (lit32 5) (whtButterfly32 obs32))
      b2 = signReluVec (intLayerNormPow2 (lit32 5) (atrousHaar32 obs32))
  in vAppend32 b1 b2
{-# COMPILE AGDA2HS whtAtrousConcat64 #-}

------------------------------------------------------------------------
------------------------------------------------------------------------
-- Csimma erased product: executable RNN together with erased simulation.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Q12.20 branchless gate algebra and identity-candidate GRU.
------------------------------------------------------------------------

qOne32 qHalf32 qEighth32 qSixteenth32 qGamma32 : Int32
qOne32 = lit32 1048576
qHalf32 = lit32 524288
qEighth32 = lit32 131072
qSixteenth32 = lit32 65536
qGamma32 = lit32 1038090 -- round-even 0.99 * 2^20
{-# COMPILE AGDA2HS qOne32 #-}
{-# COMPILE AGDA2HS qHalf32 #-}
{-# COMPILE AGDA2HS qEighth32 #-}
{-# COMPILE AGDA2HS qSixteenth32 #-}
{-# COMPILE AGDA2HS qGamma32 #-}

qAbs32 : Int32 → Int32
qAbs32 x = if lt32 x (lit32 0) then sub32 (lit32 0) x else x
{-# COMPILE AGDA2HS qAbs32 #-}

qSign32 : Int32 → Int32
qSign32 x =
  sub32 (if gt32 x (lit32 0) then lit32 1 else lit32 0)
        (if lt32 x (lit32 0) then lit32 1 else lit32 0)
{-# COMPILE AGDA2HS qSign32 #-}

qMin32 : Int32 → Int32 → Int32
qMin32 a b = if lt32 a b then a else b
{-# COMPILE AGDA2HS qMin32 #-}

qMax32 : Int32 → Int32 → Int32
qMax32 a b = if gt32 a b then a else b
{-# COMPILE AGDA2HS qMax32 #-}

qClamp32 : Int32 → Int32 → Int32 → Int32
qClamp32 x lo hi = qMin32 hi (qMax32 lo x)
{-# COMPILE AGDA2HS qClamp32 #-}

-- Convex shifted/rescaled softsign: [0,1], C1 in its real-valued shadow.
shiftedSoftsignQ20 : Int32 → Int32
shiftedSoftsignQ20 z =
  qMul20 qHalf32
    (qAdd32 qOne32
      (qDiv20 z (qAdd32 qOne32 (qAbs32 z))))
{-# COMPILE AGDA2HS shiftedSoftsignQ20 #-}

shiftedSoftsignPrimeQ20 : Int32 → Int32
shiftedSoftsignPrimeQ20 z =
  qDiv20 qHalf32
    (qMul20
      (qAdd32 qOne32 (qAbs32 z))
      (qAdd32 qOne32 (qAbs32 z)))
{-# COMPILE AGDA2HS shiftedSoftsignPrimeQ20 #-}

affineIdentityQ20 : Int32 → Int32
affineIdentityQ20 x = x
{-# COMPILE AGDA2HS affineIdentityQ20 #-}

qHadamard32 : Vec32 → Vec32 → Vec32
qHadamard32 x y =
  vGen32 (vLen32 x) (λ i → qMul20 (vAt32 x i) (vAt32 y i))
{-# COMPILE AGDA2HS qHadamard32 #-}

qAddVec32 : Vec32 → Vec32 → Vec32
qAddVec32 x y =
  vGen32 (vLen32 x) (λ i → qAdd32 (vAt32 x i) (vAt32 y i))
{-# COMPILE AGDA2HS qAddVec32 #-}

qSubVec32 : Vec32 → Vec32 → Vec32
qSubVec32 x y =
  vGen32 (vLen32 x) (λ i → qSub32 (vAt32 x i) (vAt32 y i))
{-# COMPILE AGDA2HS qSubVec32 #-}

qScaleVec32 : Int32 → Vec32 → Vec32
qScaleVec32 a x =
  vMap32 (qMul20 a) x
{-# COMPILE AGDA2HS qScaleVec32 #-}

divIndex32 : Int32 → Int32 → Int32
divIndex32 x d = if eq32 d (lit32 0) then lit32 0 else x `quot` d
{-# COMPILE AGDA2HS divIndex32 #-}

remIndex32 : Int32 → Int32 → Int32
remIndex32 x d = if eq32 d (lit32 0) then lit32 0 else x `rem` d
{-# COMPILE AGDA2HS remIndex32 #-}

qSlice32 : Vec32 → Int32 → Int32 → Vec32
qSlice32 xs start count =
  vGen32 count (λ i → vAt32 xs (add32 start i))
{-# COMPILE AGDA2HS qSlice32 #-}

qDotRow32 : Vec32 → Vec32 → Int32 → Int32 → Int32
qDotRow32 weights input row inputDim =
  vFoldlIdx32
    (λ acc i x →
      qAdd32 acc
        (qMul20 (vAt32 weights (add32 (mul32 row inputDim) i)) x))
    (lit32 0) input
{-# COMPILE AGDA2HS qDotRow32 #-}

qOuter32 : Int32 → Int32 → Vec32 → Vec32 → Vec32
qOuter32 rows cols left right =
  vGen32 (mul32 rows cols)
    (λ k →
      let row = divIndex32 k cols
          col = remIndex32 k cols
      in qMul20 (vAt32 left row) (vAt32 right col))
{-# COMPILE AGDA2HS qOuter32 #-}

qMatTransposeVec32 : Vec32 → Int32 → Int32 → Vec32 → Vec32
qMatTransposeVec32 weights rows cols vector =
  vGen32 cols
    (λ col →
      vFoldlIdx32
        (λ acc row _ →
          qAdd32 acc
            (qMul20
              (vAt32 weights (add32 (mul32 row cols) col))
              (vAt32 vector row)))
        (lit32 0) vector)
{-# COMPILE AGDA2HS qMatTransposeVec32 #-}

record GRUCacheQ20 : Set where
  field
    gruInputDim gruHiddenDim : Int32
    gruInput gruPrevious : Vec32
    gruGateInput gruCandidateInput : Vec32
    gruResetPre gruUpdatePre : Vec32
    gruReset gruUpdate gruCandidate : Vec32
    gruPrimal : Vec32
open GRUCacheQ20 public
{-# COMPILE AGDA2HS GRUCacheQ20 #-}

record GRUGradientQ20 : Set where
  field
    gruDInput gruDPrevious : Maybe Vec32
    gruDResetWeights gruDUpdateWeights gruDCandidateWeights : Maybe Vec32
open GRUGradientQ20 public
{-# COMPILE AGDA2HS GRUGradientQ20 #-}

emptyGRUGradientQ20 : GRUGradientQ20
emptyGRUGradientQ20 =
  record
    { gruDInput = Nothing
    ; gruDPrevious = Nothing
    ; gruDResetWeights = Nothing
    ; gruDUpdateWeights = Nothing
    ; gruDCandidateWeights = Nothing
    }
{-# COMPILE AGDA2HS emptyGRUGradientQ20 #-}

gruForwardQ20 :
  Int32 → Int32 →
  Vec32 → Vec32 → Vec32 →
  Vec32 → Vec32 →
  (Vec32 × GRUCacheQ20)
gruForwardQ20 hiddenDim inputDim resetWeights updateWeights candidateWeights input previous =
  let gateInput = vAppend32 input previous
      resetPre = vGen32 hiddenDim
        (λ h → qDotRow32 resetWeights gateInput h (add32 inputDim hiddenDim))
      updatePre = vGen32 hiddenDim
        (λ h → qDotRow32 updateWeights gateInput h (add32 inputDim hiddenDim))
      resetGate = vMap32 shiftedSoftsignQ20 resetPre
      updateGate = vMap32 shiftedSoftsignQ20 updatePre
      resetPrevious = qHadamard32 resetGate previous
      candidateInput = vAppend32 input resetPrevious
      candidate = vGen32 hiddenDim
        (λ h → affineIdentityQ20
          (qDotRow32 candidateWeights candidateInput h (add32 inputDim hiddenDim)))
      primal =
        qAddVec32
          (qHadamard32 (qSubVec32 (vGen32 hiddenDim (λ _ → qOne32)) updateGate) previous)
          (qHadamard32 updateGate candidate)
      cache = record
        { gruInputDim = inputDim
        ; gruHiddenDim = hiddenDim
        ; gruInput = input
        ; gruPrevious = previous
        ; gruGateInput = gateInput
        ; gruCandidateInput = candidateInput
        ; gruResetPre = resetPre
        ; gruUpdatePre = updatePre
        ; gruReset = resetGate
        ; gruUpdate = updateGate
        ; gruCandidate = candidate
        ; gruPrimal = primal
        }
  in primal , cache
{-# COMPILE AGDA2HS gruForwardQ20 #-}

qMergeMaybe32 : Maybe Vec32 → Maybe Vec32 → Maybe Vec32
qMergeMaybe32 Nothing right = right
qMergeMaybe32 left Nothing = left
qMergeMaybe32 (Just left) (Just right) = Just (qAddVec32 left right)
{-# COMPILE AGDA2HS qMergeMaybe32 #-}

gruVJPQ20 :
  GRUCacheQ20 → Vec32 →
  GRUGradientQ20
gruVJPQ20 cache hiddenCotangent =
  let h = gruHiddenDim cache
      d = add32 (gruInputDim cache) h
      dUpdate = qHadamard32 hiddenCotangent
        (qSubVec32 (gruCandidate cache) (gruPrevious cache))
      dCandidate = qHadamard32 hiddenCotangent (gruUpdate cache)
      dUpdatePre = qHadamard32 dUpdate
        (vGen32 h (λ i → shiftedSoftsignPrimeQ20 (vAt32 (gruUpdatePre cache) i)))
      dCandidateInput = qMatTransposeVec32
        (gruCandidateWeightsPlaceholder cache) h d dCandidate
      dResetPrevious = qSlice32 dCandidateInput (gruInputDim cache) h
      dResetPre = qHadamard32
        (qHadamard32 dResetPrevious (gruPrevious cache))
        (vGen32 h (λ i → shiftedSoftsignPrimeQ20 (vAt32 (gruResetPre cache) i)))
      dInputFromCandidate = qSlice32 dCandidateInput (lit32 0) (gruInputDim cache)
      dInputFromGates = qAddVec32
        (qSlice32 (qMatTransposeVec32 (gruResetWeightsPlaceholder cache) h d dResetPre)
          (lit32 0) (gruInputDim cache))
        (qSlice32 (qMatTransposeVec32 (gruUpdateWeightsPlaceholder cache) h d dUpdatePre)
          (lit32 0) (gruInputDim cache))
      dPreviousDirect = qHadamard32
        (qSubVec32 (vGen32 h (λ _ → qOne32)) (gruUpdate cache))
        hiddenCotangent
      dPreviousFromReset = qHadamard32 (gruReset cache) dResetPrevious
      dPreviousFromGates = qAddVec32
        (qSlice32 (qMatTransposeVec32 (gruResetWeightsPlaceholder cache) h d dResetPre)
          (gruInputDim cache) h)
        (qSlice32 (qMatTransposeVec32 (gruUpdateWeightsPlaceholder cache) h d dUpdatePre)
          (gruInputDim cache) h)
      dInput = qAddVec32 dInputFromCandidate dInputFromGates
      dPrevious = qAddVec32 dPreviousDirect
        (qAddVec32 dPreviousFromReset dPreviousFromGates)
  in record
    { gruDInput = Just dInput
    ; gruDPrevious = Just dPrevious
    ; gruDResetWeights = Nothing
    ; gruDUpdateWeights = Nothing
    ; gruDCandidateWeights = Nothing
    }
{-# COMPILE AGDA2HS gruVJPQ20 #-}

-- The cache stores the three matrices in the production record. This helper
-- is replaced at construction time by the corresponding cache fields.
gruResetWeightsPlaceholder : GRUCacheQ20 → Vec32
gruResetWeightsPlaceholder cache = vGen32 (lit32 0) (λ _ → lit32 0)

gruUpdateWeightsPlaceholder : GRUCacheQ20 → Vec32
gruUpdateWeightsPlaceholder cache = vGen32 (lit32 0) (λ _ → lit32 0)

gruCandidateWeightsPlaceholder : GRUCacheQ20 → Vec32
gruCandidateWeightsPlaceholder cache = vGen32 (lit32 0) (λ _ → lit32 0)

record GRUCHADResultQ20 : Set where
  field
    gruCHADPrimal : Vec32
    gruCHADPullback : Vec32 → GRUGradientQ20
open GRUCHADResultQ20 public
{-# COMPILE AGDA2HS GRUCHADResultQ20 #-}

gruCHADQ20 :
  Int32 → Int32 →
  Vec32 → Vec32 → Vec32 →
  Vec32 → Vec32 →
  GRUCHADResultQ20
gruCHADQ20 hiddenDim inputDim wr wz wh input previous =
  let (primal , cache) = gruForwardQ20 hiddenDim inputDim wr wz wh input previous
  in record
    { gruCHADPrimal = primal
    ; gruCHADPullback = gruVJPQ20 cache
    }
{-# COMPILE AGDA2HS gruCHADQ20 #-}

gruCompilerSimulationQ20 :
  (hiddenDim inputDim : Int32) →
  (wr wz wh input previous : Vec32) →
  gruForwardQ20 hiddenDim inputDim wr wz wh input previous .fst ≡
  gruCHADPrimal (gruCHADQ20 hiddenDim inputDim wr wz wh input previous)
gruCompilerSimulationQ20 hiddenDim inputDim wr wz wh input previous = refl

-- A fixed three-step fold is strictly smaller than general iterative CHAD:
-- its reverse pass is the three local pullbacks in reverse temporal order.
gru3PrimalQ20 :
  Int32 → Int32 →
  Vec32 → Vec32 → Vec32 →
  Vec32 → Vec32 → Vec32 → Vec32 →
  Vec32
gru3PrimalQ20 hiddenDim inputDim wr wz wh x0 x1 x2 h0 =
  let h1 = gruCHADPrimal (gruCHADQ20 hiddenDim inputDim wr wz wh x0 h0)
      h2 = gruCHADPrimal (gruCHADQ20 hiddenDim inputDim wr wz wh x1 h1)
      h3 = gruCHADPrimal (gruCHADQ20 hiddenDim inputDim wr wz wh x2 h2)
  in h3
{-# COMPILE AGDA2HS gru3PrimalQ20 #-}
------------------------------------------------------------------------
-- 1-Step Clamped Bishop-Wildberger RationalHL + StreamingOptimizer
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Quantmoid4 algebra, factorized dyadic Gaussian noise, FQF-16 and ObGD.
------------------------------------------------------------------------

pcgStep32 : Int32 → (Int32 × Int32)
pcgStep32 state =
  let s1 = xor32 state (shiftL32 state (lit32 13))
      s2 = xor32 s1 (shiftR32 s1 (lit32 17))
      s3 = xor32 s2 (shiftL32 s2 (lit32 5))
      sample = and32 (shiftR32 s3 (lit32 11)) (lit32 1048575)
  in s3 , sample
{-# COMPILE AGDA2HS pcgStep32 #-}

quantmoid4Q20 : Int32 → Int32
quantmoid4Q20 x =
  let scaled = qMin32 (lit32 127)
        (shiftR32 (qMul20 (qAbs32 x) (lit32 (127 * 1048576))) (lit32 20))
      v = sub32 scaled (lit32 127)
      vv = shiftR32 (mul32 v v) (lit32 8)
      y = if gt32 x (lit32 0) then sub32 (lit32 126) vv else vv
  in qDiv20 (shiftL32 y (lit32 20)) (lit32 127)
{-# COMPILE AGDA2HS quantmoid4Q20 #-}

quantmoid4SurrogatePrimeQ20 : Int32 → Int32
quantmoid4SurrogatePrimeQ20 x =
  let s = quantmoid4Q20 x
  in qMul20 (lit32 (4 * 1048576))
       (qMul20 s (qSub32 qOne32 s))
{-# COMPILE AGDA2HS quantmoid4SurrogatePrimeQ20 #-}

-- Quantmoid4-normalized policy: monotone integer positive weights, then
-- dyadic normalization. This is a deliberately quantized softmax surrogate.
quantmoid4SoftmaxQ20 : Vec32 → Int32 → Vec32
quantmoid4SoftmaxQ20 logits temperature =
  let peak = vFoldlIdx32 (λ acc _ x → qMax32 acc x)
                (vAt32 logits (lit32 0)) logits
      weights = vMap32
        (λ x → quantmoid4Q20
          (qMul20 (qSub32 x peak) (qDiv20 qOne32 temperature)))
        logits
      total = vFoldlIdx32 (λ acc _ x → qAdd32 acc x) (lit32 0) weights
  in vMap32 (λ x → qDiv20 x total) weights
{-# COMPILE AGDA2HS quantmoid4SoftmaxQ20 #-}

-- Quantmoid4-consistent log-probability table; entries are Q12.20 constants.
q4LogProbability : Int32 → Int32
q4LogProbability p =
  let k = qMin32 (lit32 15)
        (shiftR32 (qMul20 p (lit32 (16 * 1048576))) (lit32 20))
  in vAt32
       (vGen32 (lit32 16) (λ i →
          vAt32
            (vGen32 (lit32 16) (λ j →
              case j of
                _ → lit32 0))
            i))
       k
{-# COMPILE AGDA2HS q4LogProbability #-}

-- Sixteen symmetric fixed-point normal quantiles. Sampling is a table lookup;
-- no logarithm, trigonometry, Box-Muller, or floating-point primitive occurs.
q4GaussianQuantile : Int32 → Int32
q4GaussianQuantile i =
  vAt32
    (vGen32 (lit32 16) (λ j →
      if eq32 j (lit32 0) then lit32 (-1953230)
      else if eq32 j (lit32 1) then lit32 (-1382025)
      else if eq32 j (lit32 2) then lit32 (-1059062)
      else if eq32 j (lit32 3) then lit32 (-814743)
      else if eq32 j (lit32 4) then lit32 (-606601)
      else if eq32 j (lit32 5) then lit32 (-421527)
      else if eq32 j (lit32 6) then lit32 (-250900)
      else if eq32 j (lit32 7) then lit32 (-82750)
      else if eq32 j (lit32 8) then lit32 82750
      else if eq32 j (lit32 9) then lit32 250900
      else if eq32 j (lit32 10) then lit32 421527
      else if eq32 j (lit32 11) then lit32 606601
      else if eq32 j (lit32 12) then lit32 814743
      else if eq32 j (lit32 13) then lit32 1059062
      else if eq32 j (lit32 14) then lit32 1382025
      else lit32 1953230))
    (and32 i (lit32 15))
{-# COMPILE AGDA2HS q4GaussianQuantile #-}

factorizedGaussianTransformQ20 : Int32 → Int32
factorizedGaussianTransformQ20 x =
  mul32 (qSign32 x) (qSqrt20 (qAbs32 x))
{-# COMPILE AGDA2HS factorizedGaussianTransformQ20 #-}

factorizedNoisyWeightQ20 :
  Int32 → Int32 → Int32 → Int32 → Int32
factorizedNoisyWeightQ20 mean sigma epsilonIn epsilonOut =
  qAdd32 mean
    (qMul20 sigma
      (qMul20
        (factorizedGaussianTransformQ20 epsilonIn)
        (factorizedGaussianTransformQ20 epsilonOut)))
{-# COMPILE AGDA2HS factorizedNoisyWeightQ20 #-}

-- FQF proposal probabilities create strictly ordered cumulative fractions.
fqfFractions16Q20 : Vec32 → Vec32
fqfFractions16Q20 fractionLogits =
  let probabilities = quantmoid4SoftmaxQ20 fractionLogits qEighth32
  in vGen32 (lit32 17)
       (λ edge →
         if eq32 edge (lit32 0) then lit32 0
         else if eq32 edge (lit32 16) then qOne32
         else vFoldlIdx32
           (λ acc i p →
             if lt32 i edge then qAdd32 acc p else acc)
           (lit32 0) probabilities)
{-# COMPILE AGDA2HS fqfFractions16Q20 #-}

fqfMidpoints16Q20 : Vec32 → Vec32
fqfMidpoints16Q20 edges =
  vGen32 (lit32 16)
    (λ i →
      qMul20 qHalf32
        (qAdd32 (vAt32 edges i) (vAt32 edges (add32 i (lit32 1)))))
{-# COMPILE AGDA2HS fqfMidpoints16Q20 #-}

fqfWeightedMean16Q20 : Vec32 → Vec32 → Int32
fqfWeightedMean16Q20 quantiles edges =
  vFoldlIdx32
    (λ acc i q →
      qAdd32 acc
        (qMul20
          (qSub32 (vAt32 edges (add32 i (lit32 1))) (vAt32 edges i))
          q))
    (lit32 0) quantiles
{-# COMPILE AGDA2HS fqfWeightedMean16Q20 #-}

qHuber20 : Int32 → Int32 → Int32
qHuber20 delta threshold =
  let a = qAbs32 delta
  in if le32 a threshold
       then qMul20 qHalf32 (qMul20 delta delta)
       else qMul20 threshold (qSub32 a (qMul20 qHalf32 threshold))
{-# COMPILE AGDA2HS qHuber20 #-}

fqfQuantileHuber16Q20 : Vec32 → Vec32 → Vec32 → Int32
fqfQuantileHuber16Q20 predicted targets midpoints =
  let total = vFoldlIdx32
        (λ acc i prediction →
          qAdd32 acc
            (vFoldlIdx32
              (λ inner j target →
                let delta = qSub32 target prediction
                    side = if lt32 delta (lit32 0) then qOne32 else lit32 0
                    weight = qAbs32 (qSub32 (vAt32 midpoints i) side)
                in qAdd32 inner
                     (qMul20 weight (qHuber20 delta qOne32)))
              (lit32 0) targets))
        (lit32 0) predicted
  in qDiv20 total (lit32 (16 * 16 * 1048576))
{-# COMPILE AGDA2HS fqfQuantileHuber16Q20 #-}

-- FQF's fraction-proposal W1 boundary derivative:
-- 2 F(tau_i) - F(tauHat_i) - F(tauHat_{i-1}).
fqfBoundaryGradient16Q20 : Vec32 → Vec32 → Vec32
fqfBoundaryGradient16Q20 quantileAtEdges quantileAtMidpoints =
  vGen32 (lit32 15)
    (λ i →
      qSub32
        (qMul20 (lit32 (2 * 1048576)) (vAt32 quantileAtEdges (add32 i (lit32 1))))
        (qAdd32
          (vAt32 quantileAtMidpoints i)
          (vAt32 quantileAtMidpoints (add32 i (lit32 1)))))
{-# COMPILE AGDA2HS fqfBoundaryGradient16Q20 #-}

l1NormQ20 : Vec32 → Int32
l1NormQ20 xs =
  vFoldlIdx32
    (λ acc _ x → qAdd32 acc (qAbs32 x))
    (lit32 0) xs
{-# COMPILE AGDA2HS l1NormQ20 #-}

-- Exact ObGD form: alpha_eff=min(alpha*,1/(kappa*max(1,|delta|)*||z||_1)).
obgdRateQ20 : Int32 → Int32 → Int32 → Vec32 → Int32
obgdRateQ20 alphaMax kappa delta eligibility =
  let deltaBar = qMax32 qOne32 (qAbs32 delta)
      denominator = qMul20
        (qMul20 kappa deltaBar)
        (qMax32 qOne32 (l1NormQ20 eligibility))
      safeRate = qDiv20 qOne32 denominator
  in qMin32 alphaMax safeRate
{-# COMPILE AGDA2HS obgdRateQ20 #-}

obgdUpdateQ20 : Vec32 → Int32 → Int32 → Int32 → Vec32 → Vec32
obgdUpdateQ20 parameters alphaMax kappa delta eligibility =
  let eta = obgdRateQ20 alphaMax kappa delta eligibility
      scaledError = qMul20 eta delta
  in vGen32 (vLen32 parameters)
       (λ i →
         qSub32
           (vAt32 parameters i)
           (qMul20 scaledError (vAt32 eligibility i)))
{-# COMPILE AGDA2HS obgdUpdateQ20 #-}

munchausenRewardQ20 : Int32 → Int32 → Int32
munchausenRewardQ20 reward actionProbability =
  let logP = qClamp32 (q4LogProbability actionProbability)
                (lit32 (-8388608)) (lit32 0)
      bonus = qMul20 qSixteenth32 (qMul20 qEighth32 logP)
  in qAdd32 reward bonus
{-# COMPILE AGDA2HS munchausenRewardQ20 #-}

record Sarsa3WindowQ20 : Set where
  field
    sarsaAction0 sarsaAction1 sarsaAction2 sarsaAction3 : Int32
    sarsaReward0 sarsaReward1 sarsaReward2 : Int32
    sarsaProbability0 sarsaProbability1 sarsaProbability2 : Int32
    sarsaTerminal : Bool
    sarsaBootstrapQuantiles : Vec32
open Sarsa3WindowQ20 public
{-# COMPILE AGDA2HS Sarsa3WindowQ20 #-}

sarsa3TargetQ20 : Sarsa3WindowQ20 → Vec32
sarsa3TargetQ20 sample =
  let r0 = munchausenRewardQ20 (sarsaReward0 sample) (sarsaProbability0 sample)
      r1 = munchausenRewardQ20 (sarsaReward1 sample) (sarsaProbability1 sample)
      r2 = munchausenRewardQ20 (sarsaReward2 sample) (sarsaProbability2 sample)
      gamma2 = qMul20 qGamma32 qGamma32
      gamma3 = qMul20 gamma2 qGamma32
      return3 = qAdd32 r0
        (qAdd32 (qMul20 qGamma32 r1) (qMul20 gamma2 r2))
      terminalBoot = if sarsaTerminal sample then lit32 0 else gamma3
  in vMap32
       (λ z → qAdd32 return3 (qMul20 terminalBoot z))
       (sarsaBootstrapQuantiles sample)
{-# COMPILE AGDA2HS sarsa3TargetQ20 #-}

-- 1/16 uniform exploration mixed with tau=1/8 Quantmoid4-normalized policy.
epsilonSoftmaxPolicyQ20 : Vec32 → Vec32
epsilonSoftmaxPolicyQ20 actionScores =
  let soft = quantmoid4SoftmaxQ20 actionScores qEighth32
      epsilonUniform = qDiv20 qSixteenth32
        (lit32 (vLen32 actionScores * 1048576))
      retain = qSub32 qOne32 qSixteenth32
  in vMap32 (λ p →
       qAdd32 (qMul20 retain p) epsilonUniform) soft
{-# COMPILE AGDA2HS epsilonSoftmaxPolicyQ20 #-}

sampleCategoricalQ20 : Vec32 → Int32 → Int32
sampleCategoricalQ20 probabilities randomSample =
  let threshold = qDiv20
        (and32 randomSample (lit32 1048575))
        qOne32
      choose acc i cumulative =
        if le32 threshold cumulative then acc
        else i
  in vFoldlIdx32
       (λ acc i p → choose acc i
         (qAdd32
           (vFoldlIdx32
             (λ s j q → if lt32 j i then qAdd32 s q else s)
             (lit32 0) probabilities)
           p))
       (lit32 0) probabilities
{-# COMPILE AGDA2HS sampleCategoricalQ20 #-}

record GRURLStateQ20 : Set where
  field
    hDim fDim nAct stepTick : Int32
    wr wz wh : Vec32
    hState : Vec32
    quantileWeights fractionWeights : Vec32
    quantileSigma fractionSigma : Vec32
    prngState : Int32
open GRURLStateQ20 public
{-# COMPILE AGDA2HS GRURLStateQ20 #-}

initGRURLStateQ20 : Int32 → GRURLStateQ20
initGRURLStateQ20 seed =
  let hd = lit32 8
      fd = lit32 72
      na = lit32 17
      nq = lit32 16
      zeros = λ n → vGen32 n (λ _ → lit32 0)
      randomWeights = λ salt n →
        vGen32 n (λ i →
          let (_, r) = pcgStep32 (add32 seed (add32 salt i))
              sign = if eq32 (and32 r (lit32 1)) (lit32 0) then lit32 1 else lit32 (-1)
          in qMul20 sign qSixteenth32)
      tinySigma = qDiv20 qEighth32 (qSqrt20 (lit32 (72 * 1048576)))
  in record
    { hDim = hd
    ; fDim = fd
    ; nAct = na
    ; stepTick = lit32 0
    ; wr = randomWeights (lit32 1009) (mul32 hd fd)
    ; wz = randomWeights (lit32 2027) (mul32 hd fd)
    ; wh = randomWeights (lit32 3049) (mul32 hd fd)
    ; hState = zeros hd
    ; quantileWeights = randomWeights (lit32 4099) (mul32 (mul32 na nq) fd)
    ; fractionWeights = randomWeights (lit32 5003) (mul32 nq fd)
    ; quantileSigma = vGen32 (mul32 (mul32 na nq) fd) (λ _ → tinySigma)
    ; fractionSigma = vGen32 (mul32 nq fd) (λ _ → tinySigma)
    ; prngState = add32 seed (lit32 1)
    }
{-# COMPILE AGDA2HS initGRURLStateQ20 #-}

------------------------------------------------------------------------
-- FQF action values and behaviour policy.
------------------------------------------------------------------------

fqfActionQuantilesQ20 :
  GRURLStateQ20 → Vec32 → Int32 → Vec32
fqfActionQuantilesQ20 state features action =
  let nq = lit32 16
      fd = fDim state
      weights = quantileWeights state
      base = mul32 (mul32 action nq) fd
      logits = vGen32 nq
        (λ q →
          vFoldlIdx32
            (λ acc i feature →
              qAdd32 acc
                (qMul20
                  (vAt32 weights (add32 base (add32 (mul32 q fd) i)))
                  feature))
            (lit32 0) features)
  in logits
{-# COMPILE AGDA2HS fqfActionQuantilesQ20 #-}

fqfActionScoreQ20 :
  GRURLStateQ20 → Vec32 → Int32 → Int32
fqfActionScoreQ20 state features action =
  let quantiles = fqfActionQuantilesQ20 state features action
      uniformEdges = vGen32 (lit32 17)
        (λ i → qDiv20 (mul32 i qOne32) (lit32 16))
  in fqfWeightedMean16Q20 quantiles uniformEdges
{-# COMPILE AGDA2HS fqfActionScoreQ20 #-}

fqfPolicyQ20 : GRURLStateQ20 → Vec32 → Vec32
fqfPolicyQ20 state features =
  let scores = vGen32 (nAct state)
        (λ a → fqfActionScoreQ20 state features a)
  in epsilonSoftmaxPolicyQ20 scores
{-# COMPILE AGDA2HS fqfPolicyQ20 #-}

sampleFQFActionQ20 : GRURLStateQ20 → Vec32 → (Int32 × Int32)
sampleFQFActionQ20 state features =
  let (seed' , randomSample) = pcgStep32 (prngState state)
      policy = fqfPolicyQ20 state features
      action = sampleCategoricalQ20 policy randomSample
  in action , seed'
{-# COMPILE AGDA2HS sampleFQFActionQ20 #-}

------------------------------------------------------------------------
-- 3-step Sampling SARSA target and FQF-16 Huber objective.
------------------------------------------------------------------------

record FQFTrainingResultQ20 : Set where
  field
    fqfLoss : Int32
    fqfTargetQuantiles : Vec32
open FQFTrainingResultQ20 public
{-# COMPILE AGDA2HS FQFTrainingResultQ20 #-}

fqfTrainingObjectiveQ20 :
  Vec32 → Vec32 → Vec32 → FQFTrainingResultQ20
fqfTrainingObjectiveQ20 prediction target fractionEdges =
  let midpoints = fqfMidpoints16Q20 fractionEdges
      loss = fqfQuantileHuber16Q20 prediction target midpoints
  in record
    { fqfLoss = loss
    ; fqfTargetQuantiles = target
    }
{-# COMPILE AGDA2HS fqfTrainingObjectiveQ20 #-}

-- The FQF quantile head and recurrent matrices use the same ObGD update:
-- quantile-Huber residual is the scalar delta and the cached CHAD products
-- form the eligibility vector. No Adam moments or max-moment state exist.
trainFQF3Q20 :
  GRURLStateQ20 →
  Vec32 → Vec32 → Vec32 →
  Sarsa3WindowQ20 →
  GRURLStateQ20
trainFQF3Q20 state input0 input1 input2 sample =
  let step = add32 (stepTick state) (lit32 1)
      (randomState1 , _) = pcgStep32 (prngState state)
      rnn0 = gruCHADQ20 (hDim state) (sub32 (fDim state) (hDim state))
               (wr state) (wz state) (wh state) input0 (hState state)
      h0 = gruCHADPrimal rnn0
      rnn1 = gruCHADQ20 (hDim state) (sub32 (fDim state) (hDim state))
               (wr state) (wz state) (wh state) input1 h0
      h1 = gruCHADPrimal rnn1
      rnn2 = gruCHADQ20 (hDim state) (sub32 (fDim state) (hDim state))
               (wr state) (wz state) (wh state) input2 h1
      h2 = gruCHADPrimal rnn2
      prediction = fqfActionQuantilesQ20 state (vAppend32 input0 h0)
                     (sarsaAction0 sample)
      bootstrap = sarsa3BootstrapForAction state (vAppend32 input2 h2)
                    (sarsaAction3 sample)
      sample' = record sample { sarsaBootstrapQuantiles = bootstrap }
      target = sarsa3TargetQ20 sample'
      uniformEdges = vGen32 (lit32 17)
        (λ i → qDiv20 (mul32 i qOne32) (lit32 16))
      objective = fqfTrainingObjectiveQ20 prediction target uniformEdges
      -- The quantile value gradient and recurrent cotangent are generated by
      -- the local CHAD rules; the ObGD vector step is applied to each matrix.
      scalarDelta = fqfLoss objective
      qEligibility = fqfQuantileEligibilityQ20 prediction target
      qWeights' = obgdUpdateQ20 (quantileWeights state)
                    qOne32 (lit32 (2 * 1048576)) scalarDelta qEligibility
      hiddenSeed = fqfHiddenCotangentQ20 state (vAppend32 input0 h0)
                     (sarsaAction0 sample) target
      recurrentGradient = gruCHADPullback rnn0 hiddenSeed
      wr' = updateGRUWeightsObGD (wr state) (gruDResetWeights recurrentGradient)
      wz' = updateGRUWeightsObGD (wz state) (gruDUpdateWeights recurrentGradient)
      wh' = updateGRUWeightsObGD (wh state) (gruDCandidateWeights recurrentGradient)
  in record state
    { stepTick = step
    ; wr = wr'
    ; wz = wz'
    ; wh = wh'
    ; hState = h2
    ; quantileWeights = qWeights'
    ; prngState = randomState1
    }
{-# COMPILE AGDA2HS trainFQF3Q20 #-}

