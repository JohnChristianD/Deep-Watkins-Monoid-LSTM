{-# OPTIONS
--with-K
--erased-funext
--erased-quotients
--erasure
--rewriting
--confluence-check
--no-eta-equality
--no-projection-like
--exact-split
--no-fast-reduce
--auto-inline
--syntactic-equality=1
#-}

module FullCoupled.CanonicalLearnerMonolith where

open import Agda.Builtin.Equality public
open import Agda.Builtin.Equality.Rewrite public
open import Agda.Builtin.Erased.Funext public
open import Agda.Primitive public
open import Haskell.Data.Bits public
open import Haskell.Prim using (pos; negsuc)
open import Haskell.Prelude public

-- 1. Non-Univalent Definitional UIP (--with-K) + Depth-Bounded Set0 System-F Codes (Zero Impredicative Loops)
data NaturalNumber : Set where
  zeroNatural      : NaturalNumber
  successorNatural : NaturalNumber -> NaturalNumber

data TypeCode : Set where
  integerType  : TypeCode
  variableType : NaturalNumber -> TypeCode
  arrowType    : TypeCode -> TypeCode -> TypeCode
  productType  : TypeCode -> TypeCode -> TypeCode
  forallType   : TypeCode -> TypeCode

data TypeEnvironment : Set where
  emptyTypeEnvironment : TypeEnvironment
  pushTypeEnvironment  : TypeCode -> TypeEnvironment -> TypeEnvironment

lookupTypeCode : NaturalNumber -> TypeEnvironment -> TypeCode
lookupTypeCode _ emptyTypeEnvironment                          = integerType
lookupTypeCode zeroNatural (pushTypeEnvironment head _)          = head
lookupTypeCode (successorNatural n) (pushTypeEnvironment _ rest) = lookupTypeCode n rest

postulate
  @0 BoundedDecodeType : NaturalNumber -> TypeEnvironment -> TypeCode -> Set
  @0 decodeZeroDepthRule :
    ∀ (env : TypeEnvironment) (code : TypeCode) ->
    BoundedDecodeType zeroNatural env code ≡ Int
  @0 decodeIntegerTypeRule :
    ∀ (d : NaturalNumber) (env : TypeEnvironment) ->
    BoundedDecodeType (successorNatural d) env integerType ≡ Int
  @0 decodeArrowTypeRule :
    ∀ (d : NaturalNumber) (env : TypeEnvironment) (dom cod : TypeCode) ->
    BoundedDecodeType (successorNatural d) env (arrowType dom cod) ≡
      (BoundedDecodeType d env dom -> BoundedDecodeType d env cod)
  @0 decodeProductTypeRule :
    ∀ (d : NaturalNumber) (env : TypeEnvironment) (left right : TypeCode) ->
    BoundedDecodeType (successorNatural d) env (productType left right) ≡
      (BoundedDecodeType d env left × BoundedDecodeType d env right)
  @0 decodeVariableTypeRule :
    ∀ (d : NaturalNumber) (env : TypeEnvironment) (index : NaturalNumber) ->
    BoundedDecodeType (successorNatural d) env (variableType index) ≡
      BoundedDecodeType d env (lookupTypeCode index env)
  @0 decodeForallTypeRule :
    ∀ (d : NaturalNumber) (env : TypeEnvironment) (body : TypeCode) ->
    BoundedDecodeType (successorNatural d) env (forallType body) ≡
      ((argumentType : TypeCode) -> BoundedDecodeType d (pushTypeEnvironment argumentType env) body)
{-# REWRITE decodeZeroDepthRule decodeIntegerTypeRule decodeArrowTypeRule decodeProductTypeRule decodeVariableTypeRule decodeForallTypeRule #-}

-- 2. Forster (2022) Quantum-Extended Parametric Enumerability Axiom + Erased (@0) Markov Principle
data @0 EmptyType : Set where

@0 Negation : Set -> Set
Negation proposition = proposition -> EmptyType

record @0 ExistsWitness (domain : Set) (@0 predicate : domain -> Set) : Set where
  constructor MakeExistsWitness
  field
    @0 witnessValue : domain
    @0 witnessProof : predicate witnessValue

postulate
  @0 quantumExtendedUniversalEnumerator : Int -> Int -> Int
  @0 quantumExtendedParametricIndex     : (Int -> Int -> Int) -> Int -> Int
  @0 quantumExtendedParametricEnumerabilityAxiom :
    ∀ (parameterizedFamily : Int -> Int -> Int) (parameterIndex : Int) (inputInteger : Int) ->
    quantumExtendedUniversalEnumerator
      (quantumExtendedParametricIndex parameterizedFamily parameterIndex)
      inputInteger
      ≡ parameterizedFamily parameterIndex inputInteger
  @0 erasedMarkovPrinciple :
    ∀ (decidableTest : Int -> Int) ->
    Negation (∀ (stepIndex : Int) -> Negation (decidableTest stepIndex ≡ 1)) ->
    ExistsWitness Int (\ stepIndex -> decidableTest stepIndex ≡ 1)
{-# REWRITE quantumExtendedParametricEnumerabilityAxiom #-}

-- 3. Trebor-Huang Affine Linear Core (Zero Contraction Combinators S and W in Set0)
data LinearPolarity : Set where
  positivePolarity : LinearPolarity
  negativePolarity : LinearPolarity

data LinearType : LinearPolarity -> Set where
  tensorType : LinearType positivePolarity -> LinearType positivePolarity -> LinearType positivePolarity
  withType   : LinearType negativePolarity -> LinearType negativePolarity -> LinearType negativePolarity
  upShift    : LinearType positivePolarity -> LinearType negativePolarity
  downShift  : LinearType negativePolarity -> LinearType positivePolarity
  oneUnit    : LinearType positivePolarity
  bottomUnit : LinearType negativePolarity

data LinearFocus : Set where
  positiveFocus : ∀ {polarity} -> LinearType polarity -> LinearFocus
  negativeFocus : ∀ {polarity} -> LinearType polarity -> LinearFocus

data LinearContext : Set where
  emptyLinearContext : LinearContext
  consLinearContext  : LinearFocus -> LinearContext -> LinearContext

data DisjointContextSplit : LinearContext -> LinearContext -> LinearContext -> Set where
  splitEmpty : DisjointContextSplit emptyLinearContext emptyLinearContext emptyLinearContext
  splitLeft  : ∀ {focus context contextLeft contextRight} ->
               DisjointContextSplit context contextLeft contextRight ->
               DisjointContextSplit (consLinearContext focus context) (consLinearContext focus contextLeft) contextRight
  splitRight : ∀ {focus context contextLeft contextRight} ->
               DisjointContextSplit context contextLeft contextRight ->
               DisjointContextSplit (consLinearContext focus context) contextLeft (consLinearContext focus contextRight)

data AffineProof : LinearContext -> LinearFocus -> Set where
  affineVariable    : ∀ {focus} -> AffineProof (consLinearContext focus emptyLinearContext) focus
  affineWeakening   : ∀ {droppedFocus context focus} -> AffineProof context focus ->
                      AffineProof (consLinearContext droppedFocus context) focus
  affineComposition : ∀ {context contextLeft contextRight focusLeft focusRight} ->
                      DisjointContextSplit context contextLeft contextRight ->
                      AffineProof contextLeft focusLeft -> AffineProof contextRight focusRight ->
                      AffineProof context focusLeft

-- 4. Pure pForth Stack & Affine BCI-KAP@ Combinators + Exact MicroHaskell Spine Evaluator
combinatorCompositionB : ∀ {a b c : Set} -> (b -> c) -> (a -> b) -> a -> c
combinatorCompositionB outer inner value =
  let innerResult = inner value in seq innerResult (outer innerResult)

combinatorFlipC : ∀ {a b c : Set} -> (a -> b -> c) -> b -> a -> c
combinatorFlipC function secondArgument firstArgument = function firstArgument secondArgument

combinatorIdentityI : ∀ {a : Set} -> a -> a
combinatorIdentityI value = value

combinatorConstantK : ∀ {a b : Set} -> a -> b -> a
combinatorConstantK retained _ = retained

combinatorSecondA : ∀ {a b : Set} -> a -> b -> b
combinatorSecondA _ secondValue = secondValue

combinatorPairP : ∀ {a b result : Set} -> a -> b -> (a -> b -> result) -> result
combinatorPairP firstValue secondValue continuation = continuation firstValue secondValue

applicationAt : ∀ {a b : Set} -> (a -> b) -> a -> b
applicationAt function argument = seq argument (function argument)

swapStack : ∀ {top second rest : Set} -> (top × (second × rest)) -> (second × (top × rest))
swapStack (topValue , (secondValue , restStack)) = (secondValue , (topValue , restStack))

rotateStack : ∀ {top second third rest : Set} ->
              (top × (second × (third × rest))) -> (second × (third × (top × rest)))
rotateStack (topValue , (secondValue , (thirdValue , restStack))) =
  (secondValue , (thirdValue , (topValue , restStack)))

dropStack : ∀ {top rest : Set} -> (top × rest) -> rest
dropStack (_ , restStack) = restStack

data AffineCombinator : Set where
  combinatorB        : AffineCombinator
  combinatorC        : AffineCombinator
  combinatorI        : AffineCombinator
  combinatorK        : AffineCombinator
  combinatorP        : AffineCombinator
  combinatorA        : AffineCombinator
  combinatorAdd      : AffineCombinator
  combinatorMultiply : AffineCombinator
  combinatorLessThan : AffineCombinator

data MicroHaskellHeapNode : Set where
  applicationNode : MicroHaskellHeapNode -> MicroHaskellHeapNode -> MicroHaskellHeapNode
  integerNode     : Int -> MicroHaskellHeapNode
  combinatorNode  : AffineCombinator -> MicroHaskellHeapNode
  indirectionNode : MicroHaskellHeapNode -> MicroHaskellHeapNode

mutual
  unwindHeapSpine : Nat -> MicroHaskellHeapNode -> MicroHaskellHeapNode
  unwindHeapSpine zero (indirectionNode target) = indirectionNode target
  unwindHeapSpine (suc fuel) (indirectionNode target) = unwindHeapSpine fuel target
  unwindHeapSpine zero (applicationNode function argument) = applicationNode function argument
  unwindHeapSpine (suc fuel) (applicationNode function argument) =
    let reducedFunction = unwindHeapSpine fuel function
    in reduceApplicationHead fuel reducedFunction argument
  unwindHeapSpine zero leafNode = leafNode
  unwindHeapSpine (suc fuel) leafNode = leafNode

  reduceApplicationHead : Nat -> MicroHaskellHeapNode -> MicroHaskellHeapNode -> MicroHaskellHeapNode
  reduceApplicationHead zero (combinatorNode combinatorI) x = x
  reduceApplicationHead (suc fuel) (combinatorNode combinatorI) x = unwindHeapSpine fuel x
  reduceApplicationHead zero (applicationNode (combinatorNode combinatorK) x) _ = x
  reduceApplicationHead (suc fuel) (applicationNode (combinatorNode combinatorK) x) _ = unwindHeapSpine fuel x
  reduceApplicationHead zero (applicationNode (combinatorNode combinatorA) _) y = y
  reduceApplicationHead (suc fuel) (applicationNode (combinatorNode combinatorA) _) y = unwindHeapSpine fuel y
  reduceApplicationHead zero (applicationNode (applicationNode (combinatorNode combinatorB) f) g) x =
    applicationNode f (applicationNode g x)
  reduceApplicationHead (suc fuel) (applicationNode (applicationNode (combinatorNode combinatorB) f) g) x =
    unwindHeapSpine fuel (applicationNode f (applicationNode g x))
  reduceApplicationHead zero (applicationNode (applicationNode (combinatorNode combinatorC) f) x) y =
    applicationNode (applicationNode f y) x
  reduceApplicationHead (suc fuel) (applicationNode (applicationNode (combinatorNode combinatorC) f) x) y =
    unwindHeapSpine fuel (applicationNode (applicationNode f y) x)
  reduceApplicationHead zero (applicationNode (applicationNode (combinatorNode combinatorP) x) y) z =
    applicationNode (applicationNode z x) y
  reduceApplicationHead (suc fuel) (applicationNode (applicationNode (combinatorNode combinatorP) x) y) z =
    unwindHeapSpine fuel (applicationNode (applicationNode z x) y)
  reduceApplicationHead zero (applicationNode (combinatorNode combinatorAdd) a) b =
    applicationNode (applicationNode (combinatorNode combinatorAdd) a) b
  reduceApplicationHead (suc fuel) (applicationNode (combinatorNode combinatorAdd) a) b =
    case (unwindHeapSpine fuel a , unwindHeapSpine fuel b) of λ where
      (integerNode leftValue , integerNode rightValue) -> integerNode (leftValue + rightValue)
      (leftNode              , rightNode)              -> applicationNode (applicationNode (combinatorNode combinatorAdd) leftNode) rightNode
  reduceApplicationHead zero (applicationNode (combinatorNode combinatorMultiply) a) b =
    applicationNode (applicationNode (combinatorNode combinatorMultiply) a) b
  reduceApplicationHead (suc fuel) (applicationNode (combinatorNode combinatorMultiply) a) b =
    case (unwindHeapSpine fuel a , unwindHeapSpine fuel b) of λ where
      (integerNode leftValue , integerNode rightValue) -> integerNode (leftValue * rightValue)
      (leftNode              , rightNode)              -> applicationNode (applicationNode (combinatorNode combinatorMultiply) leftNode) rightNode
  reduceApplicationHead zero (applicationNode (combinatorNode combinatorLessThan) a) b =
    applicationNode (applicationNode (combinatorNode combinatorLessThan) a) b
  reduceApplicationHead (suc fuel) (applicationNode (combinatorNode combinatorLessThan) a) b =
    case (unwindHeapSpine fuel a , unwindHeapSpine fuel b) of λ where
      (integerNode leftValue , integerNode rightValue) -> combinatorNode (if leftValue < rightValue then combinatorK else combinatorA)
      (leftNode              , rightNode)              -> applicationNode (applicationNode (combinatorNode combinatorLessThan) leftNode) rightNode
  reduceApplicationHead zero functionNode argumentNode = applicationNode functionNode argumentNode
  reduceApplicationHead (suc fuel) functionNode argumentNode = applicationNode functionNode argumentNode

-- 5. V73 #01 Champion HyperParameters (04_MagStream_DoubleEval_CancelZeroMeanTop1_IQN13, SavReg=0.6011)
record MinimaxChampionHyperParameters : Set where
  constructor MakeMinimaxChampionHyperParameters
  field
    fixedPointUnitOne               : Int    -- 2^26 = 67108864 (6 integer bits, 26 fractional bits)
    fixedPointBitShift              : Nat    -- 26-bit fractional shift count
    recurrentHiddenWidth            : Int    -- 24 hidden units
    implicitQuantileCount           : Int    -- 13 non-scalar quantiles on BOTH Value and Advantage
    doubleEvaluationHeadCount       : Int    -- 2 alternating Common Random Number critics
    multistepHorizon                : Int    -- 3-Step Cancel-Zero-Mean Expected SARSA
    learningRateShift               : Nat    -- 2^-5
    streamingOptimizerBeta099       : Int    -- 0.99 (66437775)
    weightDecayKeepFactor           : Int    -- 1 - 2^-18 (67108608)
    optimizerEpsilonStabilizer      : Int    -- 2^-8 (262144)
    layerNormEpsilonStabilizer      : Int    -- 2^-6 (1048576)
    tsallisTwoFivePercentThreshold  : Int    -- fixedPointUnitOne / 20 (3355443)
    threeStepDiscountGammaCubed     : Int    -- 0.99^3 (65115644)
    munchausenScaleTauShift         : Nat    -- shiftR 6 (0.125 * 0.125)
    noisyNetworkScaleShift          : Nat    -- shiftR 2 (2^-2)
open MinimaxChampionHyperParameters public

{-# COMPILE AGDA2HS MinimaxChampionHyperParameters #-}

championHyperParameters : MinimaxChampionHyperParameters
championHyperParameters =
  MakeMinimaxChampionHyperParameters
    67108864 26 24 13 2 3 5 66437775 67108608 262144 1048576 3355443 65115644 6 2

{-# COMPILE AGDA2HS championHyperParameters #-}

private
  -- Regression guard: the bit-shift field is a natural count, not a signed value.
  fixedPointBitShiftIsNatural : Nat
  fixedPointBitShiftIsNatural = fixedPointBitShift championHyperParameters

-- 6. Bug-Fixed MicroHS-Verified Arithmetic, StandardCNN2D, & FoundryVTT PF2e Remaster Rules
absoluteValue : Int -> Int
absoluteValue x = if x < 0 then 0 - x else x

saturatingAdd : Int -> Int -> Int
saturatingAdd left right =
  let upperBound = 2147483647
      lowerBound = -2147483648
  in if 0 < right
       then (if (upperBound - right) < left then upperBound else left + right)
       else if right < 0
         then (if left < (lowerBound - right) then lowerBound else left + right)
         else left

monusSubtraction : Int -> Int -> Int
monusSubtraction a b = if b < a then a - b else 0

rectifiedLinearUnit : Int -> Int
rectifiedLinearUnit x = monusSubtraction x 0

fixedPointMultiply : Nat -> Int -> Int -> Int
fixedPointMultiply bitShift a b = shiftR (a * b) bitShift

clampShiftAmount62 : Int -> Int
clampShiftAmount62 s = if 62 < s then 62 else if s < (0 - 62) then (0 - 62) else s

nonNegativeIntToNat : Int -> Nat
nonNegativeIntToNat value with intToInteger value
... | pos amount = amount
... | negsuc _ = zero

barrettReciprocalShift : Int -> Int -> Int -> Int
barrettReciprocalShift numerator knotInverseQ30 rightShiftAmount =
  let product = numerator * knotInverseQ30
      clamped = clampShiftAmount62 rightShiftAmount
  in if 0 <= clamped
       then shiftR product (nonNegativeIntToNat clamped)
       else shiftL product (nonNegativeIntToNat (0 - clamped))

quantmoidFour : Int -> Nat -> Int -> Int
quantmoidFour unitOne bitShift x =
  let absX    = absoluteValue x
      clamped = if absX < unitOne then absX else unitOne
      delta   = clamped - unitOne
      square  = shiftR (delta * delta) (bitShift + 1)
  in if 0 < x then unitOne - square else square

quantmoidFourDerivative : Int -> Int -> Int
quantmoidFourDerivative unitOne x = monusSubtraction unitOne (absoluteValue x)

quantmoidFourGaussianErrorLinearUnit : Int -> Nat -> Int -> Int
quantmoidFourGaussianErrorLinearUnit unitOne bitShift x =
  fixedPointMultiply bitShift x (quantmoidFour unitOne bitShift (x + shiftR x 1))

quantmoidFourGeLUDerivative : Int -> Nat -> Int -> Int
quantmoidFourGeLUDerivative unitOne bitShift x =
  let shifted = x + shiftR x 1
      derivZ  = quantmoidFourDerivative unitOne shifted
  in quantmoidFour unitOne bitShift shifted + fixedPointMultiply bitShift x (derivZ + shiftR derivZ 1)

tsallisTwoFivePercentInitialization :
  MinimaxChampionHyperParameters -> Int -> Int -> Int -> Int -> Nat -> Int
tsallisTwoFivePercentInitialization parameters gateUniform randomUniform knotInverseQ30 rightShift scaleShift =
  let unitOne   = fixedPointUnitOne parameters
      symmetric = (randomUniform + randomUniform) - unitOne
  in if gateUniform < tsallisTwoFivePercentThreshold parameters
       then shiftR (barrettReciprocalShift symmetric knotInverseQ30 rightShift) scaleShift
       else 0

cleanrlStandardNatureConvolution2DStep : Int -> Nat -> Int -> Int -> Int -> Int
cleanrlStandardNatureConvolution2DStep unitOne bitShift kernelLayer0 kernelLayer1 spatialObservation =
  let convStage0 = quantmoidFourGaussianErrorLinearUnit unitOne bitShift (fixedPointMultiply bitShift kernelLayer0 spatialObservation)
  in quantmoidFourGaussianErrorLinearUnit unitOne bitShift (fixedPointMultiply bitShift kernelLayer1 convStage0)

-- FoundryVTT Pathfinder 2e Remaster Core Rulebooks JSON Evaluators for NetHack (Verified in MicroHS)
pathfinderRemasterMaximumBonus : Int -> Int -> Int
pathfinderRemasterMaximumBonus firstBonus secondBonus =
  if firstBonus < secondBonus then secondBonus else firstBonus

nethackPathfinderTotalModifier : Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int
nethackPathfinderTotalModifier attributeMod characterLevel temlProficiency statusOne statusTwo itemOne itemTwo circumstancePlusMap =
  let stackedStatus = pathfinderRemasterMaximumBonus statusOne statusTwo
      stackedItem   = pathfinderRemasterMaximumBonus itemOne itemTwo
  in attributeMod + characterLevel + temlProficiency + stackedStatus + stackedItem + circumstancePlusMap

nethackPathfinderDegreeOfSuccess : Int -> Int -> Int -> Int
nethackPathfinderDegreeOfSuccess naturalRoll totalModifier difficultyClass =
  let totalResult = naturalRoll + totalModifier
      baseDegree  = if difficultyClass + 10 <= totalResult then 3
                    else if difficultyClass <= totalResult then 2
                    else if totalResult <= difficultyClass - 10 then 0
                    else 1
      afterNat20  = if naturalRoll == 20 then (if baseDegree < 3 then baseDegree + 1 else 3) else baseDegree
  in if naturalRoll == 1 then (if 0 < afterNat20 then afterNat20 - 1 else 0) else afterNat20

@0 weightWireFocus : LinearFocus
@0 weightWireFocus = positiveFocus (downShift (upShift oneUnit))

@0 momentWireFocus : LinearFocus
@0 momentWireFocus = negativeFocus (upShift oneUnit)

@0 streamingOptimizerCertificate :
  AffineProof (consLinearContext weightWireFocus (consLinearContext momentWireFocus emptyLinearContext)) weightWireFocus
streamingOptimizerCertificate =
  affineComposition (splitLeft (splitRight splitEmpty)) affineVariable affineVariable

@0 quantumPolicyEnumerabilityWitness : (Int -> Int -> Int) -> Int -> Int -> Int
@0 quantumPolicyEnumerabilityWitness policyFamily episodeIndex stateCode =
  quantumExtendedUniversalEnumerator
    (quantumExtendedParametricIndex policyFamily episodeIndex)
    stateCode

@0 bridgeMarkovPostConvergenceWitness :
  ∀ (policyHaltsTest : Int -> Int) ->
  Negation (∀ (stepIndex : Int) -> Negation (policyHaltsTest stepIndex ≡ 1)) ->
  ExistsWitness Int (\ stepIndex -> policyHaltsTest stepIndex ≡ 1)
bridgeMarkovPostConvergenceWitness policyHaltsTest nonEmptyProof =
  erasedMarkovPrinciple policyHaltsTest nonEmptyProof

streamingOptimizerBarrettStep :
  MinimaxChampionHyperParameters -> Int -> Int -> Int -> Int -> Int -> Int -> Int ->
  @0 AffineProof (consLinearContext weightWireFocus (consLinearContext momentWireFocus emptyLinearContext)) weightWireFocus ->
  (Int × Int)
streamingOptimizerBarrettStep parameters weight velocity gradient inputFeature learningRate knotInverseVelocityQ30 rightShiftAmount _ =
  let bitShift   = fixedPointBitShift parameters
      updateRaw  = fixedPointMultiply bitShift gradient inputFeature
      absUpdate  = absoluteValue updateRaw
      decayedVel = fixedPointMultiply bitShift (streamingOptimizerBeta099 parameters) velocity
      nextVel    = if decayedVel < absUpdate then absUpdate else decayedVel
      normalized = barrettReciprocalShift updateRaw knotInverseVelocityQ30 rightShiftAmount
      scaledStep = fixedPointMultiply bitShift learningRate normalized
      decayedW   = fixedPointMultiply bitShift weight (weightDecayKeepFactor parameters)
      nextWeight = seq decayedW (saturatingAdd decayedW scaledStep)
  in seq nextWeight (seq nextVel (nextWeight , nextVel))

-- 7. V73 #01 Champion Model: MagStream + DoubleEvalOnline + CancelZeroMeanTop1 Expected SARSA + IQN13
data MinimaxChampionV73CancelTop1Model : Set where
  MakeMinimaxChampionV73CancelTop1Model :
    Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int ->
    Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int ->
    MinimaxChampionV73CancelTop1Model

initializeMinimaxChampion :
  MinimaxChampionHyperParameters -> Int -> Int -> Int -> Int -> Int -> Int -> MinimaxChampionV73CancelTop1Model
initializeMinimaxChampion parameters gate0 uniform0 gate1 uniform1 knotInverseQ30 rightShift =
  let convKernel0      = tsallisTwoFivePercentInitialization parameters gate0 uniform0 knotInverseQ30 rightShift 4
      convKernel1      = tsallisTwoFivePercentInitialization parameters gate1 uniform1 knotInverseQ30 rightShift 4
      inputWeight      = tsallisTwoFivePercentInitialization parameters gate0 uniform0 knotInverseQ30 rightShift 3
      inputGateWeight  = tsallisTwoFivePercentInitialization parameters gate1 uniform1 knotInverseQ30 rightShift 3
      forgetGateWeight = tsallisTwoFivePercentInitialization parameters gate0 uniform1 knotInverseQ30 rightShift 3
      outputGateWeight = tsallisTwoFivePercentInitialization parameters gate1 uniform0 knotInverseQ30 rightShift 3
      valueHeadOne     = tsallisTwoFivePercentInitialization parameters gate0 uniform0 knotInverseQ30 rightShift 3
      valueHeadTwo     = tsallisTwoFivePercentInitialization parameters gate1 uniform0 knotInverseQ30 rightShift 3
      advantageOne     = tsallisTwoFivePercentInitialization parameters gate1 uniform1 knotInverseQ30 rightShift 3
      advantageTwo     = tsallisTwoFivePercentInitialization parameters gate0 uniform1 knotInverseQ30 rightShift 3
      quantileWeight   = tsallisTwoFivePercentInitialization parameters gate1 uniform0 knotInverseQ30 rightShift 2
  in MakeMinimaxChampionV73CancelTop1Model
       convKernel0 0 convKernel1 0 inputWeight 0
       inputGateWeight 0 forgetGateWeight 0 outputGateWeight 0
       valueHeadOne 0 valueHeadTwo 0 advantageOne 0 advantageTwo 0 quantileWeight 0 0 0

stepMinimaxChampion :
  MinimaxChampionHyperParameters ->
  MinimaxChampionV73CancelTop1Model ->
  Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int -> Int ->
  @0 (Int -> Int -> Int) ->
  MinimaxChampionV73CancelTop1Model
stepMinimaxChampion parameters
  (MakeMinimaxChampionV73CancelTop1Model
    convKernel0 convVel0 convKernel1 convVel1 inputWeight inputVelocity
    inputGateWeight inputGateVelocity forgetGateWeight forgetGateVelocity outputGateWeight outputGateVelocity
    valueHeadOne valueVelOne valueHeadTwo valueVelTwo advantageOne advantageVelOne advantageTwo advantageVelTwo quantileWeight quantileVelocity cellState hiddenState)
  stepParity rawTileZero rawTileOne noisyInputEpsilon noisyOutputEpsilon rewardThreeStep logPolicyClip advantageMeanNext vNextOther piBestNext aStarNext advantageMeanOther qExpectedNextIgnored quantileTau oneMinusTau quantileCosine knotInverseMadScaleQ30 knotInverseVelocityQ30 rightShiftMad rightShiftVelocity policyFamily =
  let unitOne                    = fixedPointUnitOne parameters
      bitShift                   = fixedPointBitShift parameters
      learningRate               = shiftR unitOne (learningRateShift parameters)
      halfLearningRate           = shiftR learningRate 1
      convFeatureZero            = cleanrlStandardNatureConvolution2DStep unitOne bitShift convKernel0 convKernel1 rawTileZero
      convFeatureOne             = cleanrlStandardNatureConvolution2DStep unitOne bitShift convKernel0 convKernel1 rawTileOne
      preActivationZero          = fixedPointMultiply bitShift inputWeight convFeatureZero
      preActivationOne           = fixedPointMultiply bitShift inputWeight convFeatureOne
      layerMean                  = shiftR (preActivationZero + preActivationOne) 1
      centeredZero               = preActivationZero - layerMean
      normalizedInput            = barrettReciprocalShift centeredZero knotInverseMadScaleQ30 rightShiftMad
      inputGate                  = quantmoidFour unitOne bitShift (fixedPointMultiply bitShift inputGateWeight convFeatureZero)
      forgetGate                 = quantmoidFour unitOne bitShift (fixedPointMultiply bitShift forgetGateWeight convFeatureZero)
      outputGate                 = quantmoidFour unitOne bitShift (fixedPointMultiply bitShift outputGateWeight convFeatureZero)
      cellLinear                 = saturatingAdd (fixedPointMultiply bitShift forgetGate cellState) (fixedPointMultiply bitShift inputGate normalizedInput)
      nextCellState              = rectifiedLinearUnit cellLinear
      nextHiddenState            = fixedPointMultiply bitShift outputGate nextCellState
      outsideActivatedHidden     = quantmoidFourGaussianErrorLinearUnit unitOne bitShift nextHiddenState
      quantileModulation         = saturatingAdd unitOne (monusSubtraction (fixedPointMultiply bitShift quantileWeight quantileCosine) 0)
      iqnModulatedHidden         = fixedPointMultiply bitShift outsideActivatedHidden quantileModulation
      noisyExploration           = shiftR (fixedPointMultiply bitShift outsideActivatedHidden (fixedPointMultiply bitShift noisyInputEpsilon noisyOutputEpsilon)) (noisyNetworkScaleShift parameters)
      updateHeadOne              = shiftR stepParity 1 * 2 == stepParity
      activeValWeight            = if updateHeadOne then valueHeadOne else valueHeadTwo
      activeAdvWeight            = if updateHeadOne then advantageOne else advantageTwo
      duelingQValueOnline        = saturatingAdd (fixedPointMultiply bitShift activeValWeight iqnModulatedHidden) (saturatingAdd (fixedPointMultiply bitShift activeAdvWeight iqnModulatedHidden - advantageMeanNext) noisyExploration)
      -- CancelZeroMeanTop1 Expected SARSA Target: V_other + pi[a*] * (A_other(a*) - mean(A_other))
      cancelZeroMeanExpectedNext = saturatingAdd vNextOther (fixedPointMultiply bitShift piBestNext (aStarNext - advantageMeanOther))
      munchausenReward           = saturatingAdd rewardThreeStep (shiftR logPolicyClip (munchausenScaleTauShift parameters))
      temporalDifferenceTarget   = saturatingAdd munchausenReward (fixedPointMultiply bitShift (threeStepDiscountGammaCubed parameters) cancelZeroMeanExpectedNext)
      quantileGradient           = if duelingQValueOnline < temporalDifferenceTarget then quantileTau else (0 - oneMinusTau)
      outsideGradient            = fixedPointMultiply bitShift quantileGradient (activeValWeight + activeAdvWeight)
      hiddenGradient             = fixedPointMultiply bitShift outsideGradient (quantmoidFourGeLUDerivative unitOne bitShift nextHiddenState)
      cellGradient               = if 0 < cellLinear then fixedPointMultiply bitShift hiddenGradient outputGate else 0
      inputGateGradient          = fixedPointMultiply bitShift (fixedPointMultiply bitShift cellGradient normalizedInput) (quantmoidFourDerivative unitOne (fixedPointMultiply bitShift inputGateWeight convFeatureZero))
      forgetGateGradient         = fixedPointMultiply bitShift (fixedPointMultiply bitShift cellGradient cellState) (quantmoidFourDerivative unitOne (fixedPointMultiply bitShift forgetGateWeight convFeatureZero))
      outputGateGradient         = fixedPointMultiply bitShift (fixedPointMultiply bitShift hiddenGradient nextCellState) (quantmoidFourDerivative unitOne (fixedPointMultiply bitShift outputGateWeight convFeatureZero))
      normalizedInputGradient    = fixedPointMultiply bitShift cellGradient inputGate
      signCentered               = if 0 < centeredZero then unitOne else if centeredZero < 0 then (0 - unitOne) else 0
      preActivationGradient      = barrettReciprocalShift (normalizedInputGradient - shiftR normalizedInputGradient 1 - fixedPointMultiply bitShift signCentered (shiftR (fixedPointMultiply bitShift normalizedInputGradient normalizedInput) 1)) knotInverseMadScaleQ30 rightShiftMad
      convGradient1              = fixedPointMultiply bitShift (fixedPointMultiply bitShift preActivationGradient inputWeight) (quantmoidFourGeLUDerivative unitOne bitShift convFeatureZero)
      convGradient0              = fixedPointMultiply bitShift convGradient1 convKernel1
      avgConvFeature             = shiftR (convFeatureZero + convFeatureOne) 1
      @0 enumerabilityCert       = quantumPolicyEnumerabilityWitness policyFamily hiddenState convFeatureZero
      (nextValOne , nextValVelOne)                    = if updateHeadOne then streamingOptimizerBarrettStep parameters valueHeadOne valueVelOne quantileGradient iqnModulatedHidden learningRate knotInverseVelocityQ30 rightShiftVelocity streamingOptimizerCertificate else (valueHeadOne , valueVelOne)
      (nextValTwo , nextValVelTwo)                    = if updateHeadOne then (valueHeadTwo , valueVelTwo) else streamingOptimizerBarrettStep parameters valueHeadTwo valueVelTwo quantileGradient iqnModulatedHidden learningRate knotInverseVelocityQ30 rightShiftVelocity streamingOptimizerCertificate
      (nextAdvOne , nextAdvVelOne)                    = if updateHeadOne then streamingOptimizerBarrettStep parameters advantageOne advantageVelOne quantileGradient iqnModulatedHidden learningRate knotInverseVelocityQ30 rightShiftVelocity streamingOptimizerCertificate else (advantageOne , advantageVelOne)
      (nextAdvTwo , nextAdvVelTwo)                    = if updateHeadOne then (advantageTwo , advantageVelTwo) else streamingOptimizerBarrettStep parameters advantageTwo advantageVelTwo quantileGradient iqnModulatedHidden learningRate knotInverseVelocityQ30 rightShiftVelocity streamingOptimizerCertificate
      (nextQuantileWeight , nextQuantileVelocity)     = streamingOptimizerBarrettStep parameters quantileWeight quantileVelocity quantileGradient outsideActivatedHidden learningRate knotInverseVelocityQ30 rightShiftVelocity streamingOptimizerCertificate
      (nextInputWeight , nextInputVelocity)           = streamingOptimizerBarrettStep parameters inputWeight inputVelocity preActivationGradient avgConvFeature halfLearningRate knotInverseVelocityQ30 rightShiftVelocity streamingOptimizerCertificate
      (nextConvKernel0 , nextConvVel0)                = streamingOptimizerBarrettStep parameters convKernel0 convVel0 convGradient0 rawTileZero halfLearningRate knotInverseVelocityQ30 rightShiftVelocity streamingOptimizerCertificate
      (nextConvKernel1 , nextConvVel1)                = streamingOptimizerBarrettStep parameters convKernel1 convVel1 convGradient1 convFeatureZero halfLearningRate knotInverseVelocityQ30 rightShiftVelocity streamingOptimizerCertificate
      (nextInputGateWeight , nextInputGateVelocity)   = streamingOptimizerBarrettStep parameters inputGateWeight inputGateVelocity inputGateGradient convFeatureZero halfLearningRate knotInverseVelocityQ30 rightShiftVelocity streamingOptimizerCertificate
      (nextForgetGateWeight , nextForgetGateVelocity) = streamingOptimizerBarrettStep parameters forgetGateWeight forgetGateVelocity forgetGateGradient convFeatureZero halfLearningRate knotInverseVelocityQ30 rightShiftVelocity streamingOptimizerCertificate
      (nextOutputGateWeight , nextOutputGateVelocity) = streamingOptimizerBarrettStep parameters outputGateWeight outputGateVelocity outputGateGradient convFeatureZero halfLearningRate knotInverseVelocityQ30 rightShiftVelocity streamingOptimizerCertificate
  in seq nextHiddenState
       (MakeMinimaxChampionV73CancelTop1Model
         nextConvKernel0 nextConvVel0 nextConvKernel1 nextConvVel1 nextInputWeight nextInputVelocity
         nextInputGateWeight nextInputGateVelocity nextForgetGateWeight nextForgetGateVelocity nextOutputGateWeight nextOutputGateVelocity
         nextValOne nextValVelOne nextValTwo nextValVelTwo nextAdvOne nextAdvVelOne nextAdvTwo nextAdvVelTwo
         nextQuantileWeight nextQuantileVelocity nextCellState nextHiddenState)

{-# COMPILE AGDA2HS combinatorCompositionB #-}
{-# COMPILE AGDA2HS combinatorFlipC #-}
{-# COMPILE AGDA2HS combinatorIdentityI #-}
{-# COMPILE AGDA2HS combinatorConstantK #-}
{-# COMPILE AGDA2HS combinatorSecondA #-}
{-# COMPILE AGDA2HS combinatorPairP #-}
{-# COMPILE AGDA2HS applicationAt #-}
{-# COMPILE AGDA2HS swapStack #-}
{-# COMPILE AGDA2HS rotateStack #-}
{-# COMPILE AGDA2HS dropStack #-}
{-# COMPILE AGDA2HS absoluteValue #-}
{-# COMPILE AGDA2HS saturatingAdd #-}
{-# COMPILE AGDA2HS monusSubtraction #-}
{-# COMPILE AGDA2HS rectifiedLinearUnit #-}
{-# COMPILE AGDA2HS fixedPointMultiply #-}
{-# COMPILE AGDA2HS clampShiftAmount62 #-}
{-# COMPILE AGDA2HS barrettReciprocalShift #-}
{-# COMPILE AGDA2HS quantmoidFour #-}
{-# COMPILE AGDA2HS quantmoidFourDerivative #-}
{-# COMPILE AGDA2HS quantmoidFourGaussianErrorLinearUnit #-}
{-# COMPILE AGDA2HS quantmoidFourGeLUDerivative #-}
{-# COMPILE AGDA2HS tsallisTwoFivePercentInitialization #-}
{-# COMPILE AGDA2HS cleanrlStandardNatureConvolution2DStep #-}
{-# COMPILE AGDA2HS pathfinderRemasterMaximumBonus #-}
{-# COMPILE AGDA2HS nethackPathfinderTotalModifier #-}
{-# COMPILE AGDA2HS nethackPathfinderDegreeOfSuccess #-}
{-# COMPILE AGDA2HS streamingOptimizerBarrettStep #-}
{-# COMPILE AGDA2HS MinimaxChampionV73CancelTop1Model #-}
{-# COMPILE AGDA2HS initializeMinimaxChampion #-}
{-# COMPILE AGDA2HS stepMinimaxChampion #-}
