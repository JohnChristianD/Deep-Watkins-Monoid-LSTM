{-# OPTIONS
--lossy-unification
--sized-types
--exact-split
--no-projection-like
--erased-matches
--erase-record-parameters
--prop
--confluence-check
--two-level
--rewriting
--level-universe
--cumulativity
--auto-inline
--polarity
--flat-split
--large-indices
--no-forced-argument-recursion
--with-K
--no-guardedness
--injective-type-constructors
#-}

------------------------------------------------------------------------
-- Canonical theorem semantics and emergence layer.
-- Baseline reconstruction: current imports/options over the last green body.
------------------------------------------------------------------------

module FullCoupled.TheoremsMonolith where

-- Merged external import surface; internal FullCoupled imports remain module-local.
open import Haskell.Prelude

Int : Set
Int = ℤ

infixl 31 _+Int_
_+Int_ : Int → Int → Int
_+Int_ = _ℤ+_

infixl 31 _*Int_
_*Int_ : Int → Int → Int
_*Int_ = _ℤ*_

-- Stable Agda 2.8.0.2 reflection compatibility surface.
-- Reuses TypeTopology's existing BOOL/NATURAL/LIST/SIGMA bindings instead
-- of importing Agda.Builtin.Reflection, whose dependency closure attempts
-- to install competing builtin owners.
postulate String : Set
{-# BUILTIN STRING String #-}

postulate Char : Set
{-# BUILTIN CHAR Char #-}

postulate Word64 : Set
{-# BUILTIN WORD64 Word64 #-}

postulate Float : Set
{-# BUILTIN FLOAT Float #-}

{-# BUILTIN UNIT 𝟙 #-}
{-# BUILTIN SIGMA Σ #-}

⊤ : Set
⊤ = 𝟙

tt : ⊤
tt = ⋆

module ReflectionCompat where

  postulate Name : Set
  {-# BUILTIN QNAME Name #-}

  primitive
    primQNameEquality : Name → Name → Bool
    primQNameLess : Name → Name → Bool
    primShowQName : Name → String

  postulate Meta : Set
  {-# BUILTIN AGDAMETA Meta #-}

  primitive
    primMetaEquality : Meta → Meta → Bool
    primMetaLess : Meta → Meta → Bool
    primShowMeta : Meta → String
    primMetaToNat : Meta → ℕ

  data Visibility : Set where
    visible hidden instance′ : Visibility

  data Relevance : Set where
    relevant irrelevant : Relevance

  data Quantity : Set where
    quantity-0 quantity-ω : Quantity

  data Modality : Set where
    modality : Relevance → Quantity → Modality

  data ArgInfo : Set where
    arg-info : Visibility → Modality → ArgInfo

  data Arg {a} (A : Set a) : Set a where
    arg : ArgInfo → A → Arg A

  {-# BUILTIN HIDING   Visibility #-}
  {-# BUILTIN VISIBLE  visible #-}
  {-# BUILTIN HIDDEN   hidden #-}
  {-# BUILTIN INSTANCE instance′ #-}
  {-# BUILTIN RELEVANCE Relevance #-}
  {-# BUILTIN RELEVANT relevant #-}
  {-# BUILTIN IRRELEVANT irrelevant #-}
  {-# BUILTIN QUANTITY Quantity #-}
  {-# BUILTIN QUANTITY-0 quantity-0 #-}
  {-# BUILTIN QUANTITY-ω quantity-ω #-}
  {-# BUILTIN MODALITY Modality #-}
  {-# BUILTIN MODALITY-CONSTRUCTOR modality #-}
  {-# BUILTIN ARGINFO ArgInfo #-}
  {-# BUILTIN ARGARGINFO arg-info #-}
  {-# BUILTIN ARG Arg #-}
  {-# BUILTIN ARGARG arg #-}

  data Abs {a} (A : Set a) : Set a where
    abs-arg : String → A → Abs A

  {-# BUILTIN ABS Abs #-}
  {-# BUILTIN ABSABS abs-arg #-}

  data Literal : Set where
    nat : ℕ → Literal
    word64 : Word64 → Literal
    float : Float → Literal
    char : Char → Literal
    string : String → Literal
    name : Name → Literal
    meta : Meta → Literal

  {-# BUILTIN AGDALITERAL Literal #-}
  {-# BUILTIN AGDALITNAT nat #-}
  {-# BUILTIN AGDALITWORD64 word64 #-}
  {-# BUILTIN AGDALITFLOAT float #-}
  {-# BUILTIN AGDALITCHAR char #-}
  {-# BUILTIN AGDALITSTRING string #-}
  {-# BUILTIN AGDALITQNAME name #-}
  {-# BUILTIN AGDALITMETA meta #-}

  data Term : Set
  data Sort : Set
  data Pattern : Set
  data Clause : Set

  Telescope = List (Σ String (λ _ → Arg Term))

  data Term where
    var : ℕ → List (Arg Term) → Term
    con : Name → List (Arg Term) → Term
    def : Name → List (Arg Term) → Term
    lam : Visibility → Abs Term → Term
    pat-lam : List Clause → List (Arg Term) → Term
    pi : Arg Type → Abs Type → Term
    agda-sort : Sort → Term
    lit : Literal → Term
    meta : Meta → List (Arg Term) → Term
    unknown : Term

  data Sort where
    set : Term → Sort
    lit : ℕ → Sort
    prop : Term → Sort
    propLit : ℕ → Sort
    inf : ℕ → Sort
    unknown : Sort

  data Pattern where
    con : Name → List (Arg Pattern) → Pattern
    dot : Term → Pattern
    var : ℕ → Pattern
    lit : Literal → Pattern
    proj : Name → Pattern
    absurd : ℕ → Pattern

  data Clause where
    clause : Telescope → List (Arg Pattern) → Term → Clause
    absurd-clause : Telescope → List (Arg Pattern) → Clause

  {-# BUILTIN AGDATERM Term #-}
  {-# BUILTIN AGDASORT Sort #-}
  {-# BUILTIN AGDAPATTERN Pattern #-}
  {-# BUILTIN AGDACLAUSE Clause #-}
  {-# BUILTIN AGDATERMVAR var #-}
  {-# BUILTIN AGDATERMCON con #-}
  {-# BUILTIN AGDATERMDEF def #-}
  {-# BUILTIN AGDATERMMETA meta #-}
  {-# BUILTIN AGDATERMLAM lam #-}
  {-# BUILTIN AGDATERMEXTLAM pat-lam #-}
  {-# BUILTIN AGDATERMPI pi #-}
  {-# BUILTIN AGDATERMSORT agda-sort #-}
  {-# BUILTIN AGDATERMLIT lit #-}
  {-# BUILTIN AGDATERMUNSUPPORTED unknown #-}
  {-# BUILTIN AGDASORTSET set #-}
  {-# BUILTIN AGDASORTLIT lit #-}
  {-# BUILTIN AGDASORTPROP prop #-}
  {-# BUILTIN AGDASORTPROPLIT propLit #-}
  {-# BUILTIN AGDASORTINF inf #-}
  {-# BUILTIN AGDASORTUNSUPPORTED unknown #-}
  {-# BUILTIN AGDAPATCON con #-}
  {-# BUILTIN AGDAPATDOT dot #-}
  {-# BUILTIN AGDAPATVAR var #-}
  {-# BUILTIN AGDAPATLIT lit #-}
  {-# BUILTIN AGDAPATPROJ proj #-}
  {-# BUILTIN AGDAPATABSURD absurd #-}
  {-# BUILTIN AGDACLAUSECLAUSE clause #-}
  {-# BUILTIN AGDACLAUSEABSURD absurd-clause #-}

  data ErrorPart : Set where
    strErr : String → ErrorPart
    termErr : Term → ErrorPart
    pattErr : Pattern → ErrorPart
    nameErr : Name → ErrorPart

  {-# BUILTIN AGDAERRORPART ErrorPart #-}
  {-# BUILTIN AGDAERRORPARTSTRING strErr #-}
  {-# BUILTIN AGDAERRORPARTTERM termErr #-}
  {-# BUILTIN AGDAERRORPARTPATT pattErr #-}
  {-# BUILTIN AGDAERRORPARTNAME nameErr #-}

  postulate
    TC : ∀ {a} → Set a → Set a
    returnTC : ∀ {a} {A : Set a} → A → TC A
    bindTC : ∀ {a b} {A : Set a} {B : Set b} → TC A → (A → TC B) → TC B
    unify : Term → Term → TC ⊤
    typeError : ∀ {a} {A : Set a} → List ErrorPart → TC A
    inferType : Term → TC Term
    catchTC : ∀ {a} {A : Set a} → TC A → TC A → TC A
    quoteTC : ∀ {a} {A : Set a} → A → TC Term

  {-# BUILTIN AGDATCM TC #-}
  {-# BUILTIN AGDATCMRETURN returnTC #-}
  {-# BUILTIN AGDATCMBIND bindTC #-}
  {-# BUILTIN AGDATCMUNIFY unify #-}
  {-# BUILTIN AGDATCMTYPEERROR typeError #-}
  {-# BUILTIN AGDATCMINFERTYPE inferType #-}
  {-# BUILTIN AGDATCMCATCHERROR catchTC #-}
  {-# BUILTIN AGDATCMQUOTETERM quoteTC #-}

open ReflectionCompat using
  ( Name
  ; Meta
  ; Visibility
  ; visible
  ; Relevance
  ; relevant
  ; ArgInfo
  ; arg-info
  ; Arg
  ; arg
  ; Term
  ; TC
  ; returnTC
  ; bindTC
  ; unify
  ; typeError
  ; inferType
  ; catchTC
  ; var
  ; con
  ; def
  ; pat-lam
  ; strErr
  )

try-fun : ∀ {a} {A : Set a} → TC A → TC A → TC A
try-fun = catchTC

syntax try-fun t f = try t or-else f




-- BEGIN THEOREM-SPECIFIC IMPORTS
------------------------------------------------------------------------
-- Theorem-specific imports: vendored Formal Methods in Agda.
-- Imported qualified; theorem names remain isolated from this monolith.
------------------------------------------------------------------------

-- Keep the TypeTopology sum algebra local: the synchronized imports hide
-- `_+_` to disambiguate natural/integer/rational addition.
open import MLTT.Plus renaming (_+_ to _⊎_; inl to inj₁; inr to inj₂)
open import Ordinals.Notions _<_ renaming (is-accessible to RankAccessible; acc to rankAcc)
open import FullCoupled.CanonicalLearnerMonolith as C hiding (Int; _+Int_; _*Int_; gruStep)
module MLS = C.MonoidLSTMStreams
open import Agda.Primitive using (Level)
open import Agda.Builtin.Size using (Size; Size<_; ∞)
-- END THEOREM-SPECIFIC IMPORTS

------------------------------------------------------------------------
-- Guarded trace interface and coinductive stream-fusion proof.
-- Learner transition semantics stay in CanonicalLearnerMonolith.
------------------------------------------------------------------------

record GuardedLearnerTrace {A : Set}
  (K : C.FullLearnerKernel A)
  (initial : C.FullLearnerState A) : Set₁ where
  constructor guardedLearnerTrace
  field
    learnerTrace : C.LearnerStream ∞ (C.FullLearnerState A)
    learnerTraceStartsAtInitial :
      C.learnerStreamHead learnerTrace ＝ initial

open GuardedLearnerTrace public

canonicalLearnerTraceGuarded :
  ∀ {A : Set}
    (K : C.FullLearnerKernel A)
    (initial : C.FullLearnerState A) →
  GuardedLearnerTrace K initial
canonicalLearnerTraceGuarded K initial =
  guardedLearnerTrace (C.canonicalLearnerTrace K initial) refl

learnerSpecGuardedTrace :
  ∀ {A : Set}
    (K : C.FullLearnerKernel A)
    (initial : C.FullLearnerState A) →
  GuardedLearnerTrace K initial
learnerSpecGuardedTrace = canonicalLearnerTraceGuarded

record LearnerStreamBisim (i : Size) {ℓ : Level} {A : Set ℓ}
  (left right : C.LearnerStream i A) : Set ℓ where
  coinductive
  field
    learnerStreamHeadsAgree :
      C.learnerStreamHead left ＝ C.learnerStreamHead right
    learnerStreamTailsBisimilar :
      ∀ {j : Size< i} →
      LearnerStreamBisim j
        (C.learnerStreamTail left {j})
        (C.learnerStreamTail right {j})

open LearnerStreamBisim public

-- Infinite map fusion: equality of every observable head is preserved
-- coinductively, with each recursive obligation at a smaller size.
mapStreamFusionBisim :
  {ℓA ℓB ℓD : Level} {i : Size}
  {A : Set ℓA} {B : Set ℓB} {D : Set ℓD} →
  (f : B → D) →
  (g : A → B) →
  (input : C.LearnerStream i A) →
  LearnerStreamBisim i
    (C.mapLearnerStream f (C.mapLearnerStream g input))
    (C.mapLearnerStream (λ value → f (g value)) input)
mapStreamFusionBisim f g input .learnerStreamHeadsAgree = refl
mapStreamFusionBisim f g input .learnerStreamTailsBisimilar {j} =
  mapStreamFusionBisim f g (C.learnerStreamTail input {j})

------------------------------------------------------------------------
-- Seeded scan semantics on the canonical sized stream carrier.
--
-- The seed is observable at position zero; each later state consumes one
-- input through the transition. This is the stream-level counterpart of the
-- canonical learner trace and makes state-encoding fusion a theorem-level law.
------------------------------------------------------------------------

scanLearnerStream :
  {ℓS ℓI : Level} {i : Size}
  {State : Set ℓS} {Input : Set ℓI} →
  (State → Input → State) →
  State → C.LearnerStream i Input → C.LearnerStream i State
scanLearnerStream = MLS.scanSeededStream

scanMapFusionBisim :
  {ℓS ℓT ℓI : Level} {i : Size}
  {State : Set ℓS} {Target : Set ℓT} {Input : Set ℓI} →
  (encode : State → Target) →
  (step : State → Input → State) →
  (targetStep : Target → Input → Target) →
  (stepFusion :
    (state : State) (input : Input) →
    encode (step state input) ＝ targetStep (encode state) input) →
  (state : State) (inputs : C.LearnerStream i Input) →
  LearnerStreamBisim i
    (C.mapLearnerStream encode (scanLearnerStream step state inputs))
    (scanLearnerStream targetStep (encode state) inputs)
scanMapFusionBisim encode step targetStep stepFusion state inputs
  .learnerStreamHeadsAgree = refl
scanMapFusionBisim encode step targetStep stepFusion state inputs
  .learnerStreamTailsBisimilar {j}
  rewrite sym (stepFusion state (C.learnerStreamHead inputs)) =
    scanMapFusionBisim
      encode
      step
      targetStep
      stepFusion
      (step state (C.learnerStreamHead inputs))
      (C.learnerStreamTail inputs {j})

repeatUnitLearnerStream : {i : Size} → C.LearnerStream i C.⊤
repeatUnitLearnerStream = C.learnerStreamRepeat C.tt

-- Collapse the generic seeded scan back onto the canonical monoid-LSTM
-- transition: the proof identifies every observable learner state, not just
-- the first sample or a separately redefined transition function.
canonicalLearnerTraceScan :
  {i : Size} {A : Set}
  (K : C.FullLearnerKernel A)
  (initial : C.FullLearnerState A) →
  LearnerStreamBisim i
    (C.canonicalLearnerTrace K initial)
    (scanLearnerStream
      (λ state _ → C.canonicalFullStep K state)
      initial
      repeatUnitLearnerStream)
canonicalLearnerTraceScan K initial .learnerStreamHeadsAgree = refl
canonicalLearnerTraceScan K initial .learnerStreamTailsBisimilar {j} =
  canonicalLearnerTraceScan K (C.canonicalFullStep K initial)

-- TypeTopology's falsity is 𝟘. Keep familiar theorem notation local;
-- do not import the Agda standard library or alter builtin ownership.
⊥ : Set
⊥ = 𝟘

⊥-elim : ∀ {A : Set} → ⊥ → A
⊥-elim = 𝟘-elim

------------------------------------------------------------------------
-- Scott–Strachey lifted Nat semantics, owned by the theorem monolith.
-- No --safe pragma is used: this is source consolidation, not a safe-mode
-- promise for the legacy theorem surface.
------------------------------------------------------------------------

module ScottStracheyDomains where
  open import Haskell.Prelude using (_≡_; refl)
  open import Agda.Primitive using (Level)
  import Haskell.Prelude as HP

  BNat : Set
  BNat = HP.Nat

  bzero : BNat
  bzero = HP.zero

  bsuc : BNat → BNat
  bsuc = HP.suc

  infixl 6 _b+_
  _b+_ : BNat → BNat → BNat
  _b+_ = HP._+_

  ScottEmpty : Set
  ScottEmpty = HP.⊥

  data Lift {ℓ : Level} (A : Set ℓ) : Set ℓ where
    bottom : Lift A
    defined : A → Lift A

  -- Strict lifting preserves bottom and maps defined states through the step.
  liftStrictMap :
    {ℓ : Level} {A : Set ℓ} → (A → A) → Lift A → Lift A
  liftStrictMap step bottom = bottom
  liftStrictMap step (defined value) = defined (step value)

  liftStrictMapBottom :
    {ℓ : Level} {A : Set ℓ} (step : A → A) →
    liftStrictMap step bottom ≡ bottom
  liftStrictMapBottom step = refl

  liftStrictMapDefined :
    {ℓ : Level} {A : Set ℓ} (step : A → A) (value : A) →
    liftStrictMap step (defined value) ≡ defined (step value)
  liftStrictMapDefined step value = refl

  infix 4 _⊑_

  data _⊑_ {ℓ : Level} {A : Set ℓ} :
    Lift A → Lift A → Set ℓ where
    bottomLeast : {value : Lift A} → bottom ⊑ value
    definedReflexive : {value : A} → defined value ⊑ defined value

  reflexive⊑ :
    {ℓ : Level} {A : Set ℓ} {value : Lift A} → value ⊑ value
  reflexive⊑ {value = bottom} = bottomLeast
  reflexive⊑ {value = defined value} = definedReflexive

  bottomIsLeast :
    {ℓ : Level} {A : Set ℓ} (value : Lift A) → bottom ⊑ value
  bottomIsLeast _ = bottomLeast

  bottomIsNotZero : bottom ≡ defined bzero → ScottEmpty
  bottomIsNotZero ()

  definedZeroIsNotBottom : defined bzero ≡ bottom → ScottEmpty
  definedZeroIsNotBottom ()

  definedZeroIsNotLeast : defined bzero ⊑ bottom → ScottEmpty
  definedZeroIsNotLeast ()

  data NatExpr : Set where
    numeral : BNat → NatExpr
    diverges : NatExpr
    _⊕_ : NatExpr → NatExpr → NatExpr

  infixl 6 _⊕_

  strictNatAdd : Lift BNat → Lift BNat → Lift BNat
  strictNatAdd bottom _ = bottom
  strictNatAdd (defined _) bottom = bottom
  strictNatAdd (defined left) (defined right) = defined (left b+ right)

  denote : NatExpr → Lift BNat
  denote (numeral n) = defined n
  denote diverges = bottom
  denote (left ⊕ right) = strictNatAdd (denote left) (denote right)

  definedAdditionRegression :
    denote (numeral (bsuc (bsuc bzero)) ⊕ numeral (bsuc (bsuc (bsuc bzero))))
      ≡ defined (bsuc (bsuc (bsuc (bsuc (bsuc bzero)))))
  definedAdditionRegression = refl

  divergenceAbsorbsAddition :
    denote (diverges ⊕ numeral (bsuc (bsuc (bsuc bzero)))) ≡ bottom
  divergenceAbsorbsAddition = refl

  -- Domain-theoretic regression: denotational semantics is compositional.
  -- The meaning of a compound expression is obtained by applying the lifted
  -- operator to the meanings of its subexpressions.
  denotationalCompositionalityRegression :
    ∀ (left right : NatExpr) →
      denote (left ⊕ right) ≡
        strictNatAdd (denote left) (denote right)
  denotationalCompositionalityRegression left right = refl

  -- Bottom is observable through strict lifted addition: a diverging left
  -- operand yields bottom for every right expression.
  denotationalBottomStrictnessRegression :
    (right : NatExpr) → denote (diverges ⊕ right) ≡ bottom
  denotationalBottomStrictnessRegression right = refl

  -- nLab-style Scott–Ershov regression: compositionality and bottom strictness
  -- are jointly exhibited as actual kernel-checked proof fields.
  record NLabDenotationalSemanticsRegression
    (left right : NatExpr) : Set where
    constructor nLabDenotationalSemanticsRegression
    field
      nLabCompositionality :
        denote (left ⊕ right) ≡
          strictNatAdd (denote left) (denote right)
      nLabBottomStrictness :
        denote (diverges ⊕ right) ≡ bottom

  scottErshovNLabDenotationalSemanticsRegression :
    (left right : NatExpr) →
    NLabDenotationalSemanticsRegression left right
  scottErshovNLabDenotationalSemanticsRegression left right =
    record
      { nLabCompositionality = refl
      ; nLabBottomStrictness = refl
      }

  record AlgebraOperations (A : Set) : Set₁ where
    field
      algebraZero : A
      algebraAdd : A → A → A
      algebraMultiply : A → A → A
      algebraNegate : A → A

  open AlgebraOperations public

  module StrictLiftedAlgebra {A : Set} (operations : AlgebraOperations A) where
    -- Use qualified record projections rather than opening them as shorthand.
    -- This avoids ambiguity between the local field names and the record
    -- projections exported into the surrounding scope.
    strictAdd : Lift A → Lift A → Lift A
    strictAdd bottom _ = bottom
    strictAdd (defined _) bottom = bottom
    strictAdd (defined left) (defined right) =
      defined (AlgebraOperations.algebraAdd operations left right)

    strictMultiply : Lift A → Lift A → Lift A
    strictMultiply bottom _ = bottom
    strictMultiply (defined _) bottom = bottom
    strictMultiply (defined left) (defined right) =
      defined (AlgebraOperations.algebraMultiply operations left right)

    strictNegate : Lift A → Lift A
    strictNegate bottom = bottom
    strictNegate (defined value) =
      defined (AlgebraOperations.algebraNegate operations value)

    inverseLawFailsAtBottom :
      strictAdd bottom (strictNegate bottom) ≡
        defined (AlgebraOperations.algebraZero operations) → ScottEmpty
    inverseLawFailsAtBottom ()

    zeroAnnihilatorFailsAtBottom :
      strictMultiply (defined (AlgebraOperations.algebraZero operations)) bottom ≡
        defined (AlgebraOperations.algebraZero operations) → ScottEmpty
    zeroAnnihilatorFailsAtBottom ()

------------------------------------------------------------------------
-- Scott-domain interpretation of the actual canonical learner transition.
-- This strict lift is tied to the learner's real canonicalFullStep.
------------------------------------------------------------------------

module CanonicalLearnerDenotation {A : Set}
  (K : C.FullLearnerKernel A) where
  open ScottStracheyDomains

  liftedCanonicalFullStep :
    Lift (C.FullLearnerState A) → Lift (C.FullLearnerState A)
  liftedCanonicalFullStep =
    liftStrictMap (C.canonicalFullStep K)

  canonicalLearnerDenotationBottom :
    liftedCanonicalFullStep bottom ≡ bottom
  canonicalLearnerDenotationBottom = refl

  canonicalLearnerTraceDenotationStep :
    (state : C.FullLearnerState A) →
    liftedCanonicalFullStep (defined state) ≡
      defined (C.canonicalFullStep K state)
  canonicalLearnerTraceDenotationStep state = refl

------------------------------------------------------------------------
-- Lawvere diagonal fixed points, constructive existence and boundary.
--
-- Pointwise-surjective self-application yields a fixed point for every
-- endomap. Boolean negation has no fixed point, so such a diagonal decoder
-- cannot be surjective when its result type has two distinct booleans.
-- No cubical principles or fixed-point postulates occur in this proof.
------------------------------------------------------------------------

module LawvereDiagonal where
  open import Haskell.Prelude using (_≡_; refl)
  import Haskell.Prelude as HP

  LawvereEmpty : Set
  LawvereEmpty = HP.⊥

  record DiagonalPreimage {A B : Set}
    (diagonal : A → A → B)
    (target : A → B) : Set where
    constructor diagonalPreimage
    field
      witness : A
      decodesPointwise : (x : A) → diagonal witness x ≡ target x

  record FixedPointWitness {B : Set} (f : B → B) : Set where
    constructor fixedPointWitness
    field
      fixedValue : B
      fixedEquation : f fixedValue ≡ fixedValue

  symEq : {A : Set} {x y : A} → x ≡ y → y ≡ x
  symEq refl = refl

  lawvereFixedPoint
    : {A B : Set}
      (diagonal : A → A → B)
      (surjective : (target : A → B) → DiagonalPreimage diagonal target)
      (f : B → B)
      → FixedPointWitness f
  lawvereFixedPoint diagonal surjective f
    with surjective (λ x → f (diagonal x x))
  ... | diagonalPreimage a equation =
    fixedPointWitness (diagonal a a) (symEq (equation a))

  data Boolean : Set where
    booleanFalse booleanTrue : Boolean

  booleanFlip : Boolean → Boolean
  booleanFlip booleanFalse = booleanTrue
  booleanFlip booleanTrue = booleanFalse

  noBooleanFlipFixedPoint
    : (b : Boolean) → booleanFlip b ≡ b → LawvereEmpty
  noBooleanFlipFixedPoint booleanFalse ()
  noBooleanFlipFixedPoint booleanTrue ()

  noSurjectiveBooleanDiagonal
    : {A : Set}
      (diagonal : A → A → Boolean)
      → ((target : A → Boolean) → DiagonalPreimage diagonal target)
      → LawvereEmpty
  noSurjectiveBooleanDiagonal diagonal surjective
    with lawvereFixedPoint diagonal surjective booleanFlip
  ... | fixedPointWitness value equation =
    noBooleanFlipFixedPoint value equation


------------------------------------------------------------------------
-- Re-export policy semantics proved beside the canonical learner transition.
------------------------------------------------------------------------
module BetaOptimalityBoundary = C.BetaOptimalityBoundary

-- Keep natural multiplication explicit: the synchronized import surface also
-- contains rational multiplication, so theorem algebra names TypeTopology's
-- natural operation through this local alias.
module NatMult = Naturals.Multiplication

infixl 32 _ℕ*_
_ℕ*_ : ℕ → ℕ → ℕ
_ℕ*_ = NatMult._*_


------------------------------------------------------------------------
-- Reflection compression for repeated equality transport.
-- The target equality determines the congruence function.
------------------------------------------------------------------------

𝓋𝓇𝒶 : {A : Set} → A → Arg A
𝓋𝓇𝒶 = arg (arg-info visible relevant)

＝-type-info : Term → TC (Arg Term × Arg Term × Term × Term)
＝-type-info (def (quote _＝_) (𝓁 ∷ 𝒯 ∷ arg _ l ∷ arg _ r ∷ [])) = returnTC (𝓁 , 𝒯 , l , r)
＝-type-info _ = typeError [ strErr "Term is not a ＝-type." ]

$-head : Term → Term
$-head (var v args) = var v []
$-head (con c args) = con c []
$-head (def f args) = def f []
$-head (pat-lam cs args) = pat-lam cs []
$-head t = t

macro
  apply-cong : Term → Term → TC ⊤
  apply-cong p goal =
    try
      (bindTC (inferType goal) λ τ →
        bindTC (＝-type-info τ) λ where
          (_ , _ , l , _) →
            unify goal
              (def (quote ap)
                (𝓋𝓇𝒶 ($-head l) ∷ 𝓋𝓇𝒶 p ∷ [])))
      or-else unify goal p


------------------------------------------------------------------------
-- Constructive inversion/search bridge.
--
-- The Haskell-minus-one line gives inverse computation as a
-- preimage search with an explicit correctness condition.
-- TWA's exact-real-search framework makes the search constructive by
-- requiring searchable domains and explicit uniform-continuity moduli.
--
-- This theorem layer combines those ideas without putting search,
-- inversion, or proof-discovery machinery into the learner semantics.
------------------------------------------------------------------------

module ExactSearchInversion (fe : FunExt) where

  open import TWA.Thesis.Chapter3.ClosenessSpaces fe hiding (decidable-uc-predicate)
  open import TWA.Thesis.Chapter3.SearchableTypes fe

  record SearchableEquivalence
    (X Y : ClosenessSpace 𝓤₀) : Set₁ where
    constructor searchableEquivalence
    field
      forward : ⟨ X ⟩ → ⟨ Y ⟩
      inverse : ⟨ Y ⟩ → ⟨ X ⟩
      forward-ucontinuous :
        f-ucontinuous X Y forward
      inverse-ucontinuous :
        f-ucontinuous Y X inverse
      forward-inverse :
        ∀ y → forward (inverse y) ＝ y
      inverse-forward :
        ∀ x → inverse (forward x) ＝ x
      searchable-domain :
        csearchable 𝓤₀ X

  open SearchableEquivalence public

  inverse-selects-preimage :
    ∀ {X Y : ClosenessSpace 𝓤₀}
    (E : SearchableEquivalence X Y)
    (y : ⟨ Y ⟩)
    (x : ⟨ X ⟩) →
    forward E x ＝ y →
    inverse E y ＝ x
  inverse-selects-preimage E y x h =
    trans
      (ap (inverse E) (sym h))
      (inverse-forward E x)

  forward-is-equiv :
    ∀ {X Y : ClosenessSpace 𝓤₀}
    (E : SearchableEquivalence X Y) →
    is-equiv (forward E)
  forward-is-equiv E =
    section-retraction-equiv
      (forward E)
      (inverse E , (λ y → forward-inverse E y))
      (inverse E , (λ x → inverse-forward E x))

  pullback-decidable-uc-predicate :
    ∀ {X Y : ClosenessSpace 𝓤₀}
    (E : SearchableEquivalence X Y) →
    decidable-uc-predicate 𝓤₀ Y →
    decidable-uc-predicate 𝓤₀ X
  pullback-decidable-uc-predicate E ((p , d) , ϕ) =
    ((p ∘ forward E , d ∘ forward E)
    , p-ucontinuous-comp
        _ _
        (forward E)
        (forward-ucontinuous E)
        p ϕ)

  inverse-preserves-csearchability :
    ∀ {X Y : ClosenessSpace 𝓤₀}
    (E : SearchableEquivalence X Y) →
    csearchable 𝓤₀ Y
  inverse-preserves-csearchability {X = X} {Y = Y} E ((p , d) , ϕ) =
    y₀ , γ
    where
      pulled : decidable-uc-predicate 𝓤₀ X
      pulled = pullback-decidable-uc-predicate E ((p , d) , ϕ)

      x₀ : ⟨ X ⟩
      x₀ = pr₁ (searchable-domain E pulled)

      γx :
        (Σ x ꞉ ⟨ X ⟩ , (p (forward E x)) holds) →
        p (forward E x₀) holds
      γx = pr₂ (searchable-domain E pulled)

      y₀ : ⟨ Y ⟩
      y₀ = forward E x₀

      γ :
        (Σ y ꞉ ⟨ Y ⟩ , (p y) holds) →
        p y₀ holds
      γ (y , py) =
        γx
          ( inverse E y
          , transport
              (λ z → (p z) holds)
              (forward-inverse E y ⁻¹)
              py
          )

  inverse-correct :
    ∀ {X Y : ClosenessSpace 𝓤₀}
    (E : SearchableEquivalence X Y)
    (y : ⟨ Y ⟩)
    (x : ⟨ X ⟩) →
    forward E x ＝ y →
    inverse E y ＝ x
  inverse-correct =
    inverse-selects-preimage

  inverse-csearchable :
    ∀ {X Y : ClosenessSpace 𝓤₀}
    (E : SearchableEquivalence X Y) →
    csearchable 𝓤₀ Y
  inverse-csearchable =
    inverse-preserves-csearchability

------------------------------------------------------------------------
record NatRingSolverNormalizationTheorem : Set₁ where
  constructor natRingSolverNormalizationTheorem
  field
    normalization :
      ∀ (epsilon scale : ℕ) →
      (epsilon + succ zero) * scale ＝
      (epsilon * scale) + scale

nat-ring-solver-layernorm-step :
  ∀ (epsilon scale : ℕ) →
  (epsilon + succ zero) * scale ＝
  (epsilon * scale) + scale
nat-ring-solver-layernorm-step epsilon scale =
  trans
    (distributivity-mult-over-addition' epsilon 1 scale)
    (ap (λ x → epsilon * scale + x)
      (trans (mult-commutativity 1 scale) (mult-right-id scale)))

nat-ring-solver-normalization-theorem :
  NatRingSolverNormalizationTheorem
nat-ring-solver-normalization-theorem =
  natRingSolverNormalizationTheorem nat-ring-solver-layernorm-step

record IntegerRingSolverNormalizationTheorem : Set₁ where
  constructor integerRingSolverNormalizationTheorem
  field
    normalization :
      ∀ (i j k : ℤ) →
      i ℤ+ (j ℤ+ k) ＝ (i ℤ+ j) ℤ+ k

integer-ring-solver-assoc :
  ∀ (i j k : ℤ) →
  i ℤ+ (j ℤ+ k) ＝ (i ℤ+ j) ℤ+ k
integer-ring-solver-assoc i j k =
  sym (ℤ+-assoc i j k)

integer-ring-solver-normalization-theorem :
  IntegerRingSolverNormalizationTheorem
integer-ring-solver-normalization-theorem =
  integerRingSolverNormalizationTheorem integer-ring-solver-assoc

record ListMonoidSolverNormalizationTheorem : Set₁ where
  constructor listMonoidSolverNormalizationTheorem
  field
    normalization :
      ∀ (xs ys zs : List C.IntCode) →
      xs ++ (ys ++ zs) ＝ (xs ++ ys) ++ zs

list-monoid-solver-append-assoc :
  ∀ (xs ys zs : List C.IntCode) →
  xs ++ (ys ++ zs) ＝ (xs ++ ys) ++ zs
list-monoid-solver-append-assoc xs ys zs =
  sym (++-assoc xs ys zs)

list-monoid-solver-normalization-theorem :
  ListMonoidSolverNormalizationTheorem
list-monoid-solver-normalization-theorem =
  listMonoidSolverNormalizationTheorem list-monoid-solver-append-assoc

record CanonicalAlgebraicTacticBackendTheorem : Set₁ where
  constructor canonicalAlgebraicTacticBackendTheorem
  field
    natSemiringNormalization :
      NatRingSolverNormalizationTheorem
    integerRingNormalization :
      IntegerRingSolverNormalizationTheorem
    listMonoidNormalization :
      ListMonoidSolverNormalizationTheorem

canonical-algebraic-tactic-backend-theorem :
  CanonicalAlgebraicTacticBackendTheorem
canonical-algebraic-tactic-backend-theorem =
  canonicalAlgebraicTacticBackendTheorem
    nat-ring-solver-normalization-theorem
    integer-ring-solver-normalization-theorem
    list-monoid-solver-normalization-theorem

record CanonicalSafeTacticNormalizationTheorem : Set₁ where
  constructor canonicalSafeTacticNormalizationTheorem
  field
    algebraicBackend :
      CanonicalAlgebraicTacticBackendTheorem
    natSemiringNormalization :
      ∀ (epsilon scale : ℕ) →
      (epsilon + succ zero) * scale ＝
      (epsilon * scale) + scale
    integerRingNormalization :
      ∀ (i j k : Int) →
      i + (j + k) ＝ (i + j) + k
    listMonoidNormalization :
      ∀ (xs ys zs : List C.IntCode) →
      xs ++ (ys ++ zs) ＝ (xs ++ ys) ++ zs

canonical-safe-tactic-normalization-theorem :
  CanonicalSafeTacticNormalizationTheorem
canonical-safe-tactic-normalization-theorem =
  canonicalSafeTacticNormalizationTheorem
    canonical-algebraic-tactic-backend-theorem
    nat-ring-solver-layernorm-step
    integer-ring-solver-assoc
    list-monoid-solver-append-assoc

------------------------------------------------------------------------
------------------------------------------------------------------------
-- Carrier-polymorphic statistical representation kernel.
--
-- This arithmetic-free kernel remains because later ZPF representation
-- theorems depend on its left-inverse and injectivity facts.
--
-- The representation theorem is structural. External statistical
-- literature motivates possible instantiations; it is not imported as an
-- Agda proof source.
------------------------------------------------------------------------


record CarrierPolymorphicStatisticalRepresentation
  (State Observation : Set) : Set₁ where
  constructor carrierPolymorphicStatisticalRepresentation
  field
    encode : State → Observation
    decode : Observation → State
    decodeEncode : ∀ s → decode (encode s) ＝ s

open CarrierPolymorphicStatisticalRepresentation public

statisticalEncodeInjective :
  ∀ {State Observation : Set}
  (R : CarrierPolymorphicStatisticalRepresentation State Observation)
  {s t : State} →
  encode R s ＝ encode R t →
  s ＝ t
statisticalEncodeInjective R eq = ap (decode R) eq

statisticalEncodeDistinguishes :
  ∀ {State Observation : Set}
  (R : CarrierPolymorphicStatisticalRepresentation State Observation)
  {s t : State} →
  s ≠ t →
  encode R s ≠ encode R t
statisticalEncodeDistinguishes R distinct collision =
  distinct (statisticalEncodeInjective R collision)

------------------------------------------------------------------------
-- Canonical theorem section: GRU statistical representation and injectivity.
------------------------------------------------------------------------

module GRUStatisticalInjectivity where
-- TypeTopology's pinned Spartan surface has equality and negation but does not
-- export inequality notation. Derive it locally to avoid widening the synchronized
-- import block and introducing another import-closure conflict.
infix 4 _≢_
_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = ¬ (x ＝ y)

CanonicalGRUStatisticalObservation : Set
CanonicalGRUStatisticalObservation = C.GRUState × (C.CanonicalToken → C.IntCode)
canonicalGRUStatisticalEncode : C.GRUState → CanonicalGRUStatisticalObservation
canonicalGRUStatisticalEncode s = s , (λ _ → C.hiddenState s)
canonicalGRUStatisticalDecode : CanonicalGRUStatisticalObservation → C.GRUState
canonicalGRUStatisticalDecode observation = pr₁ observation
canonicalGRUStatisticalDecodeEncode : ∀ s → canonicalGRUStatisticalDecode (canonicalGRUStatisticalEncode s) ＝ s
canonicalGRUStatisticalDecodeEncode s = refl
leftInverse-implies-injective :
  ∀ {State Feature : Set}
  (observe : State → Feature)
  (inverse : Feature → State) →
  (∀ s → inverse (observe s) ＝ s) →
  ∀ {s t} → observe s ＝ observe t → s ＝ t
leftInverse-implies-injective observe inverse leftInverse eq =
  trans
    (sym (leftInverse _))
    (trans
      apply-cong eq
      (leftInverse _))

canonicalGRUStatisticalEncodeLeftInverse :
  ∀ s →
  canonicalGRUStatisticalDecode (canonicalGRUStatisticalEncode s) ＝ s
canonicalGRUStatisticalEncodeLeftInverse =
  canonicalGRUStatisticalDecodeEncode

canonicalGRUStatisticalEncodeInjective :
  ∀ {s t : C.GRUState} →
  canonicalGRUStatisticalEncode s ＝ canonicalGRUStatisticalEncode t →
  s ＝ t
canonicalGRUStatisticalEncodeInjective =
  leftInverse-implies-injective
    canonicalGRUStatisticalEncode
    canonicalGRUStatisticalDecode
    canonicalGRUStatisticalEncodeLeftInverse
record CanonicalGRUStatisticalInjectivityTheorem : Set₁ where
  constructor canonicalGRUStatisticalInjectivityTheorem
  field
    encode : C.GRUState → CanonicalGRUStatisticalObservation
    decode : CanonicalGRUStatisticalObservation → C.GRUState
    decodeEncode : ∀ s → decode (encode s) ＝ s
    injective : ∀ {s t : C.GRUState} → encode s ＝ encode t → s ＝ t
canonical-gru-statistical-injectivity-theorem : CanonicalGRUStatisticalInjectivityTheorem
canonical-gru-statistical-injectivity-theorem = canonicalGRUStatisticalInjectivityTheorem canonicalGRUStatisticalEncode canonicalGRUStatisticalDecode canonicalGRUStatisticalDecodeEncode canonicalGRUStatisticalEncodeInjective
canonicalGRUStatisticalDistinguishability : ∀ {s t : C.GRUState} → s ≢ t → canonicalGRUStatisticalEncode s ≢ canonicalGRUStatisticalEncode t
canonicalGRUStatisticalDistinguishability distinct collision = distinct (canonicalGRUStatisticalEncodeInjective collision)
canonicalGRUStatisticalStepConsequence : ∀ (s : C.GRUState) (x : C.IntCode) → canonicalGRUStatisticalEncode (C.gruStep s x) ＝ (C.gruStep s x , (λ _ → C.hiddenState (C.gruStep s x)))
canonicalGRUStatisticalStepConsequence s x = refl

identityActivation8-injective :
  ∀ {x y : C.IntCode} →
  C.identityActivation8 x ＝ C.identityActivation8 y →
  x ＝ y
identityActivation8-injective eq = eq

------------------------------------------------------------------------
------------------------------------------------------------------------
-- Canonical theorem section: ZPF statistical representation boundary.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Typed ZPF / omega^3 semantic boundary for the canonical GRU layer.
--
-- The physical ZPF carrier, Maxwell constraints, stochastic semantics,
-- and spectral convention are explicit inputs.  The module does not
-- manufacture a physical ZPF inhabitant.
--
-- The omega^3 law is represented by an explicit frequency multiplication
-- operation, a proof that omegaCubed is the triple product, and a
-- spectral-density normalization carrier.  A concrete instantiation decides
-- the frequency measure and normalization (for example, per unit angular
-- frequency) without introducing a new arithmetic dependency here.
--
-- Once a ZPF -> canonical-GRU statistical representation supplies
-- decode (encode z) == z, global injectivity follows from the existing
-- carrier-polymorphic statistical representation theorem.
------------------------------------------------------------------------


record ZPFOmegaCubedSpectralLaw
  (ZPFState Frequency SpectralDensity : Set)
  (frequencyMultiply : Frequency → Frequency → Frequency) : Set₁ where
  constructor zpfOmegaCubedSpectralLaw
  field
    density :
      ZPFState → Frequency → SpectralDensity
    spectralDensityOfOmegaCubed :
      Frequency → SpectralDensity
    omegaCubed :
      Frequency → Frequency
    omegaCubedDefinition :
      ∀ (ω : Frequency) →
      omegaCubed ω ＝
      frequencyMultiply (frequencyMultiply ω ω) ω
    omegaCubedLaw :
      ∀ (z : ZPFState) (ω : Frequency) →
      density z ω ＝ spectralDensityOfOmegaCubed (omegaCubed ω)

open ZPFOmegaCubedSpectralLaw public

record ZPFMaxwellSemanticData
  (ZPFState MaxwellField Frequency SpectralDensity : Set)
  (frequencyMultiply : Frequency → Frequency → Frequency)
  (Homogeneous Isotropic Maxwell : MaxwellField → Set)
  (Stochastic : ZPFState → Set) : Set₁ where
  constructor zpfMaxwellSemanticData
  field
    fieldZPF :
      ZPFState → MaxwellField
    homogeneous :
      ∀ z → Homogeneous (fieldZPF z)
    isotropic :
      ∀ z → Isotropic (fieldZPF z)
    stochastic :
      ∀ z → Stochastic z
    maxwell :
      ∀ z → Maxwell (fieldZPF z)
    spectralLaw :
      ZPFOmegaCubedSpectralLaw
        ZPFState
        Frequency
        SpectralDensity
        frequencyMultiply

open ZPFMaxwellSemanticData public

record ZPFGRUStatisticalRepresentation
  (ZPFState Frequency SpectralDensity MaxwellField : Set)
  (frequencyMultiply : Frequency → Frequency → Frequency)
  (Homogeneous Isotropic Maxwell : MaxwellField → Set)
  (Stochastic : ZPFState → Set) : Set₁ where
  constructor zpfGRUStatisticalRepresentation
  field
    zpfSemantics :
      ZPFMaxwellSemanticData
        ZPFState
        MaxwellField
        Frequency
        SpectralDensity
        frequencyMultiply
        Homogeneous
        Isotropic
        Maxwell
        Stochastic
    statisticalRepresentation :
      CarrierPolymorphicStatisticalRepresentation
        ZPFState
        CanonicalGRUStatisticalObservation

open ZPFGRUStatisticalRepresentation public

zpfGRUStatisticalEncodeInjective :
  ∀ {ZPFState Frequency SpectralDensity MaxwellField : Set}
  {frequencyMultiply : Frequency → Frequency → Frequency}
  {Homogeneous Isotropic Maxwell : MaxwellField → Set}
  {Stochastic : ZPFState → Set}
  (R :
    ZPFGRUStatisticalRepresentation
      ZPFState
      Frequency
      SpectralDensity
      MaxwellField
      frequencyMultiply
      Homogeneous
      Isotropic
      Maxwell
      Stochastic)
  {z₁ z₂ : ZPFState} →
  encode (statisticalRepresentation R) z₁ ＝
  encode (statisticalRepresentation R) z₂ →
  z₁ ＝ z₂
zpfGRUStatisticalEncodeInjective R =
  statisticalEncodeInjective (statisticalRepresentation R)

zpfGRUStatisticalDistinguishes :
  ∀ {ZPFState Frequency SpectralDensity MaxwellField : Set}
  {frequencyMultiply : Frequency → Frequency → Frequency}
  {Homogeneous Isotropic Maxwell : MaxwellField → Set}
  {Stochastic : ZPFState → Set}
  (R :
    ZPFGRUStatisticalRepresentation
      ZPFState
      Frequency
      SpectralDensity
      MaxwellField
      frequencyMultiply
      Homogeneous
      Isotropic
      Maxwell
      Stochastic)
  {z₁ z₂ : ZPFState} →
  z₁ ≢ z₂ →
  encode (statisticalRepresentation R) z₁ ≢
  encode (statisticalRepresentation R) z₂
zpfGRUStatisticalDistinguishes R =
  statisticalEncodeDistinguishes (statisticalRepresentation R)

record ZPFGRUGlobalInjectivityTheorem
  (ZPFState Frequency SpectralDensity MaxwellField : Set)
  (frequencyMultiply : Frequency → Frequency → Frequency)
  (Homogeneous Isotropic Maxwell : MaxwellField → Set)
  (Stochastic : ZPFState → Set) : Set₁ where
  constructor zpfGRUGlobalInjectivityTheoremWitness
  field
    representation :
      ZPFGRUStatisticalRepresentation
        ZPFState
        Frequency
        SpectralDensity
        MaxwellField
        frequencyMultiply
        Homogeneous
        Isotropic
        Maxwell
        Stochastic
    globalInjective :
      ∀ {z₁ z₂ : ZPFState} →
      encode (statisticalRepresentation representation) z₁ ＝
      encode (statisticalRepresentation representation) z₂ →
      z₁ ＝ z₂

zpfGRUGlobalInjectivityTheorem :
  ∀ {ZPFState Frequency SpectralDensity MaxwellField : Set}
  {frequencyMultiply : Frequency → Frequency → Frequency}
  {Homogeneous Isotropic Maxwell : MaxwellField → Set}
  {Stochastic : ZPFState → Set} →
  ZPFGRUStatisticalRepresentation
    ZPFState
    Frequency
    SpectralDensity
    MaxwellField
    frequencyMultiply
    Homogeneous
    Isotropic
    Maxwell
    Stochastic →
  ZPFGRUGlobalInjectivityTheorem
    ZPFState
    Frequency
    SpectralDensity
    MaxwellField
    frequencyMultiply
    Homogeneous
    Isotropic
    Maxwell
    Stochastic
zpfGRUGlobalInjectivityTheorem R =
  zpfGRUGlobalInjectivityTheoremWitness
    R
    (zpfGRUStatisticalEncodeInjective R)

------------------------------------------------------------------------
-- Canonical theorem section: semantic e-graph transport.
------------------------------------------------------------------------

{-
  Proof-only e-graph semantic transport.

  This module does not implement an e-graph data structure and does not
  manufacture any physical witness. It gives the existing commuting-square
  architecture a small semantic interface: an e-graph congruence is sound
  when its related expressions have equal interpretations. Once that
  semantic equality is available, ordinary Agda congruence transports it
  through the existing learner/physical maps.

  The intended use is to connect symbolic equality-saturation artifacts to
  the canonical theorem layer without treating graph membership as a proof
  of a physical law.
-}


------------------------------------------------------------------------
-- Abstract e-graph congruence.
------------------------------------------------------------------------

record EGraphCongruence (Expression : Set) : Set₁ where
  constructor eGraphCongruence
  field
    related : Expression → Expression → Set

    related-refl :
      ∀ e →
      related e e

    related-sym :
      ∀ {e f} →
      related e f →
      related f e

    related-trans :
      ∀ {e f g} →
      related e f →
      related f g →
      related e g

open EGraphCongruence public

------------------------------------------------------------------------
-- Semantic interpretation of an e-graph congruence.
--
-- Soundness is the only bridge required here: graph equivalence is not
-- silently identified with definitional equality.
------------------------------------------------------------------------

record EGraphSemanticInterpretation
  (Expression State : Set) : Set₁ where
  constructor eGraphSemanticInterpretation
  field
    congruence : EGraphCongruence Expression
    interpret : Expression → State
    sound :
      ∀ {e f} →
      related congruence e f →
      interpret e ＝ interpret f

open EGraphSemanticInterpretation public

------------------------------------------------------------------------
-- Basic semantic closure of graph equivalence.
------------------------------------------------------------------------

eGraph-sound-refl :
  ∀ {Expression State : Set}
  (R : EGraphSemanticInterpretation Expression State) →
  ∀ e →
  interpret R e ＝ interpret R e
eGraph-sound-refl R e = refl

eGraph-sound-sym :
  ∀ {Expression State : Set}
  (R : EGraphSemanticInterpretation Expression State)
  {e f : Expression} →
  related (congruence R) e f →
  interpret R f ＝ interpret R e
eGraph-sound-sym R h = sym (sound R h)

eGraph-sound-trans :
  ∀ {Expression State : Set}
  (R : EGraphSemanticInterpretation Expression State)
  {e f g : Expression} →
  related (congruence R) e f →
  related (congruence R) f g →
  interpret R e ＝ interpret R g
eGraph-sound-trans R h₁ h₂ =
  trans (sound R h₁) (sound R h₂)

------------------------------------------------------------------------
-- Contextual transport.
--
-- If a state transformation is a semantic context, e-graph equality can
-- be pushed through it by ordinary equality congruence. This is the
-- semantic kernel consumed by commuting-square and iterate/prefix proofs.
------------------------------------------------------------------------

eGraph-context :
  ∀ {Expression State Context : Set}
  (R : EGraphSemanticInterpretation Expression State)
  (context : State → Context) →
  ∀ {e f : Expression} →
  related (congruence R) e f →
  context (interpret R e) ＝ context (interpret R f)
eGraph-context R context h =
  ap context (sound R h)

eGraph-rewrite-context :
  ∀ {Expression State : Set}
  (R : EGraphSemanticInterpretation Expression State)
  (step : State → State) →
  ∀ {e f : Expression} →
  related (congruence R) e f →
  step (interpret R e) ＝ step (interpret R f)
eGraph-rewrite-context R step h =
  ap step (sound R h)

------------------------------------------------------------------------
-- The semantic e-graph contract is deliberately proof-only. It closes
-- graph-level equality transport, while the concrete Law I/Law III and
-- physics-to-learner witness records remain separate obligations.
------------------------------------------------------------------------


------------------------------------------------------------------------
-- Cost-guided e-graph paths.
--
-- A* is a search strategy, not a proof rule.  The semantic proof is the
-- path of sound e-graph edges; the ℕ cost is carried separately so an
-- A*-style selector can optimize traversal without changing the proof.
------------------------------------------------------------------------


record AStarCostModel (Expression : Set) : Set₁ where
  constructor aStarCostModel
  field
    edgeCost : Expression → Expression → ℕ
    heuristic : Expression → ℕ

open AStarCostModel public

data EGraphSemanticPath
  {Expression State : Set}
  (R : EGraphSemanticInterpretation Expression State) :
  Expression → Expression → Set where
  path-refl :
    ∀ e →
    EGraphSemanticPath R e e
  path-step :
    ∀ {e f g} →
    related (congruence R) e f →
    EGraphSemanticPath R f g →
    EGraphSemanticPath R e g

eGraph-path-sound :
  ∀ {Expression State : Set}
  (R : EGraphSemanticInterpretation Expression State) →
  ∀ {e f} →
  EGraphSemanticPath R e f →
  interpret R e ＝ interpret R f
eGraph-path-sound R (path-refl e) = refl
eGraph-path-sound R (path-step h rest) =
  trans (sound R h) (eGraph-path-sound R rest)

eGraph-path-trans :
  ∀ {Expression State : Set}
  {R : EGraphSemanticInterpretation Expression State}
  {e f g : Expression} →
  EGraphSemanticPath R e f →
  EGraphSemanticPath R f g →
  EGraphSemanticPath R e g
eGraph-path-trans (path-refl e) rest = rest
eGraph-path-trans (path-step h rest) tail =
  path-step h (eGraph-path-trans rest tail)

data SemanticEdgeStatus : Set where
  semanticProved : SemanticEdgeStatus
  semanticConditional : SemanticEdgeStatus
  semanticFrontier : SemanticEdgeStatus
  semanticBlockedByCounterexample : SemanticEdgeStatus

data SemanticEdgeEvidence : Set where
  kernelProof : SemanticEdgeEvidence
  discoveryArtifact : SemanticEdgeEvidence
  externalLiterature : SemanticEdgeEvidence

record SemanticEdgeMetadata : Set₁ where
  constructor semanticEdgeMetadata
  field
    source : String
    target : String
    proofIdentifier : String
    assumptions : List String
    status : SemanticEdgeStatus
    evidence : SemanticEdgeEvidence
    unconditional : Bool

record CertifiedEGraphEdge
  {Expression State : Set}
  (R : EGraphSemanticInterpretation Expression State)
  (lhs rhs : Expression) : Set₁ where
  constructor certifiedEGraphEdge
  field
    metadata : SemanticEdgeMetadata
    path : EGraphSemanticPath R lhs rhs

open CertifiedEGraphEdge public

eGraph-certified-edge-sound :
  ∀ {Expression State : Set}
  {R : EGraphSemanticInterpretation Expression State}
  {lhs rhs : Expression} →
  CertifiedEGraphEdge R lhs rhs →
  interpret R lhs ＝ interpret R rhs
eGraph-certified-edge-sound edge =
  eGraph-path-sound _ (path edge)


record AStarSemanticClosure
  (Expression State : Set) : Set₁ where
  constructor aStarSemanticClosure
  field
    semantics : EGraphSemanticInterpretation Expression State
    costs : AStarCostModel Expression

open AStarSemanticClosure public

-- A* supplies candidate ordering/cost metadata, but semantic closure is
-- justified solely by the soundness theorem for an explicit e-graph path.
aStar-guided-semantic-closure :
  ∀ {Expression State : Set}
  (A : AStarSemanticClosure Expression State) →
  ∀ {e f : Expression} →
  EGraphSemanticPath (semantics A) e f →
  interpret (semantics A) e ＝ interpret (semantics A) f
aStar-guided-semantic-closure A =
  eGraph-path-sound (semantics A)

------------------------------------------------------------------------
-- Haskell-like algebraic structure for A* candidate plans.
--
-- The candidate-plan carrier is List Expression, with concatenation as
-- the monoid operation. This algebra is separate from semantic equality:
-- it describes composition of discovered plans, while e-graph soundness
-- remains the source of endpoint equality.
------------------------------------------------------------------------

record AStarPlanMonoidTheorem (Expression : Set) : Set₁ where
  constructor aStarPlanMonoidTheorem
  field
    appendAssociative :
      ∀ (xs ys zs : List Expression) →
      (xs ++ ys) ++ zs ＝ xs ++ (ys ++ zs)
    appendIdentityLeft :
      ∀ (xs : List Expression) →
      [] ++ xs ＝ xs
    appendIdentityRight :
      ∀ (xs : List Expression) →
      xs ++ [] ＝ xs

open AStarPlanMonoidTheorem public

aStar-plan-append-associative :
  ∀ {Expression : Set} →
  ∀ (xs ys zs : List Expression) →
  (xs ++ ys) ++ zs ＝ xs ++ (ys ++ zs)
aStar-plan-append-associative xs ys zs =
  ++-assoc xs ys zs

aStar-plan-append-identity-left :
  ∀ {Expression : Set} →
  ∀ (xs : List Expression) →
  [] ++ xs ＝ xs
aStar-plan-append-identity-left xs = refl

aStar-plan-append-identity-right :
  ∀ {Expression : Set} →
  ∀ (xs : List Expression) →
  xs ++ [] ＝ xs
aStar-plan-append-identity-right [] = refl
aStar-plan-append-identity-right (x ∷ xs) =
  ap (x ∷_) (aStar-plan-append-identity-right xs)

aStar-plan-monoid-theorem :
  ∀ (Expression : Set) →
  AStarPlanMonoidTheorem Expression
aStar-plan-monoid-theorem Expression =
  aStarPlanMonoidTheorem
    aStar-plan-append-associative
    aStar-plan-append-identity-left
    aStar-plan-append-identity-right

------------------------------------------------------------------------
-- Haskell-like monadic search surface.
--
-- State carries the A* frontier; List supplies candidate-plan
-- nondeterminism. This is an operational adapter only. Semantic equality
-- still comes from sound e-graph paths, and RawMonad does not itself carry
-- monad-law proofs in the standard library.
------------------------------------------------------------------------

record AStarRawMonad (M : Set → Set) : Set₁ where
  constructor aStarRawMonad
  field
    returnM : ∀ {A : Set} → A → M A
    bindM : ∀ {A B : Set} → M A → (A → M B) → M B

AStarState : Set → Set → Set
AStarState S A = S → A × S

aStarStateReturn : ∀ {S A : Set} → A → AStarState S A
aStarStateReturn value state = value , state

aStarStateBind :
  ∀ {S A B : Set} →
  AStarState S A →
  (A → AStarState S B) →
  AStarState S B
aStarStateBind action next state =
  next (pr₁ (action state)) (pr₂ (action state))

aStarStateRawMonad :
  ∀ {S : Set} →
  AStarRawMonad (AStarState S)
aStarStateRawMonad =
  aStarRawMonad aStarStateReturn aStarStateBind

aStarListReturn : ∀ {A : Set} → A → List A
aStarListReturn value = value ∷ []

aStarListBind :
  ∀ {A B : Set} →
  List A →
  (A → List B) →
  List B
aStarListBind [] f = []
aStarListBind (x ∷ xs) f = f x ++ aStarListBind xs f

aStarListRawMonad : AStarRawMonad List
aStarListRawMonad =
  aStarRawMonad aStarListReturn aStarListBind

record AStarHaskellMonadSurface (Expression : Set) : Set₁ where
  constructor aStarHaskellMonadSurface
  field
    frontierMonad :
      AStarRawMonad (AStarState (List (List Expression)))
    candidatePlanMonad :
      AStarRawMonad List

open AStarHaskellMonadSurface public

aStar-frontier-monad :
  ∀ {Expression : Set} →
  AStarRawMonad (AStarState (List (List Expression)))
aStar-frontier-monad = aStarStateRawMonad

aStar-candidate-plan-monad :
  ∀ {Expression : Set} →
  AStarRawMonad List
aStar-candidate-plan-monad = aStarListRawMonad

aStar-haskell-monad-surface :
  ∀ (Expression : Set) →
  AStarHaskellMonadSurface Expression
aStar-haskell-monad-surface Expression =
  aStarHaskellMonadSurface
    aStar-frontier-monad
    aStar-candidate-plan-monad

------------------------------------------------------------------------
-- The cost/heuristic fields are intentionally not used in the equality
-- proof.  This prevents A* from becoming an unsound source of semantic
-- equality while still giving the discovery layer a typed cost-guidance
-- object that can be attached to a sound e-graph interpretation.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Canonical theorem section: repository-wide semantic e-graph closure.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Repository-wide semantic e-graph closure.
--
-- This module closes the semantic layer for every indexed Agda module
-- without pretending that module names or search costs are physical laws.
-- A module contributes a sound interpretation; e-graph paths then compose
-- exact semantic equality, and A* supplies traversal cost/heuristic data
-- without entering the equality proof.
--
-- The repository index below is deliberately finite and explicit.  It names
-- the two surviving authority files on this branch.  The
-- closure theorem is still parametric in the semantic interpretation for
-- each file: enumeration does not manufacture semantic soundness.
------------------------------------------------------------------------


data RepositoryAgdaModule : Set where
  canonicalLearnerMonolith :
    RepositoryAgdaModule
  theoremsMonolith :
    RepositoryAgdaModule

record AgdaSemanticModuleFamily : Set₁ where
  constructor agdaSemanticModuleFamily
  field
    Expression : RepositoryAgdaModule → Set
    moduleState : RepositoryAgdaModule → Set
    closure :
      (m : RepositoryAgdaModule) →
      AStarSemanticClosure
        (Expression m)
        (moduleState m)

open AgdaSemanticModuleFamily public

repositoryAgdaAStarSemanticClosure :
  (F : AgdaSemanticModuleFamily)
  (m : RepositoryAgdaModule)
  {e f : Expression F m} →
  EGraphSemanticPath
    (semantics (closure F m))
    e
    f →
  interpret (semantics (closure F m)) e
  ＝
  interpret (semantics (closure F m)) f
repositoryAgdaAStarSemanticClosure F m =
  aStar-guided-semantic-closure (closure F m)

record UnconditionalAgdaEGraphAStarClosure : Set₁ where
  constructor unconditionalAgdaEGraphAStarClosure
  field
    closeAll :
      (F : AgdaSemanticModuleFamily)
      (m : RepositoryAgdaModule)
      {e f : Expression F m} →
      EGraphSemanticPath
        (semantics (closure F m))
        e
        f →
      interpret (semantics (closure F m)) e
      ＝
      interpret (semantics (closure F m)) f

unconditional-agda-egraph-astar-closure :
  UnconditionalAgdaEGraphAStarClosure

unconditional-agda-egraph-astar-closure =
  unconditionalAgdaEGraphAStarClosure
    repositoryAgdaAStarSemanticClosure

------------------------------------------------------------------------
-- Conditional convergence closure for e-graph/A* search.
--
-- The witness deliberately separates three obligations:
--   * rank/descent: a finite ℕ measure for search-state progress,
--   * eventualStable/stableNext: the actual termination/stabilization fact,
--   * stablePath: semantic equality supplied by the e-graph.
--
-- A* cost/heuristic data remains guidance only. It is never used as
-- equality or convergence evidence.
------------------------------------------------------------------------

eGraphAStarIterate :
  ∀ {State : Set} →
  (State → State) →
  ℕ →
  State →
  State
eGraphAStarIterate step zero s = s
eGraphAStarIterate step (succ n) s =
  eGraphAStarIterate step n (step s)

record EGraphAStarFiniteRankConvergenceWitness
  (Expression State : Set) : Set₁ where
  constructor eGraphAStarFiniteRankConvergenceWitness
  field
    closure :
      AStarSemanticClosure Expression State
    step :
      State → State
    candidate :
      State → Expression
    target :
      Expression
    stable :
      State → Set
    rank :
      State → ℕ
    rankZero :
      ∀ s → rank s ＝ zero → stable s
    strictDescent :
      ∀ s → ¬ stable s →
      rank (step s) < rank s
    stableNext :
      ∀ s → stable s → stable (step s)
    eventualStable :
      ∀ s →
      Σ ℕ
        (λ n →
          stable
            (eGraphAStarIterate
              step
              n
              s))
    stablePath :
      ∀ {s} →
      stable s →
      EGraphSemanticPath
        (semantics closure)
        (candidate s)
        target

open EGraphAStarFiniteRankConvergenceWitness public

eGraphAStarConvergenceSemanticClosure :
  ∀ {Expression State : Set} →
  (W : EGraphAStarFiniteRankConvergenceWitness Expression State) →
  ∀ s →
  Σ ℕ
    (λ n →
      interpret
        (semantics (closure W))
        (candidate W
          (eGraphAStarIterate
            (step W)
            n
            s))
      ＝
      interpret
        (semantics (closure W))
        (target W))
eGraphAStarConvergenceSemanticClosure W s
  with eventualStable W s
... | n , stableAtN =
  n ,
  eGraph-path-sound
    (semantics (closure W))
    (stablePath W stableAtN)

------------------------------------------------------------------------
-- Rank + strict descent can now discharge eventual stability once the
-- stable predicate is decidable. The ℕ measure is consumed through
-- TypeTopology's well-founded accessibility structure; no search
-- cost or heuristic is used as semantic evidence.
------------------------------------------------------------------------

eGraphAStarEventualStableFromRank :
  ∀ {Expression State : Set}
  (W : EGraphAStarFiniteRankConvergenceWitness Expression State) →
  (∀ s → stable W s ⊎ ¬ stable W s) →
  ∀ s →
  Σ ℕ
    (λ n →
      stable W
        (eGraphAStarIterate
          (step W)
          n
          s))
eGraphAStarEventualStableFromRank {Expression = Expression} {State = State} W stableOrNot s =
  go s (rank W s) refl (<-is-well-founded (rank W s))
  where
  go :
    ∀ (s : State) (n : ℕ) →
    rank W s ＝ n →
    RankAccessible n →
    Σ ℕ
      (λ k →
        stable W
          (eGraphAStarIterate
            (step W)
            k
            s))
  go s n rankEq (rankAcc smaller) with stableOrNot s
  ... | inj₁ stableS =
    zero , stableS
  ... | inj₂ notStable with strictDescent W s notStable
  ... | descent with
    go
      (step W s)
      (rank W (step W s))
      refl
      (smaller (transport (λ k → rank W (step W s) < k) rankEq descent))
  ... | n′ , stableAtN′ =
    succ n′ , stableAtN′

eGraphAStarStablePathPersists :
  ∀ {Expression State : Set}
  (W : EGraphAStarFiniteRankConvergenceWitness Expression State)
  {s : State} →
  stable W s →
  ∀ n →
  stable W
    (eGraphAStarIterate
      (step W)
      n
      s)
eGraphAStarStablePathPersists W stableS zero = stableS
eGraphAStarStablePathPersists W {s = s} stableS (succ n) =
  eGraphAStarStablePathPersists
    W
    (stableNext W s stableS)
    n


------------------------------------------------------------------------
-- Concrete integer LayerNorm E-Graph / A* semantic closure.
--
-- The expression language exposes equivalent representations of the same
-- exact integer statistics.  The semantic relation is interpretation
-- equality, while A* contributes only traversal cost/heuristic data.
-- Thus every A* path remains proof-relevant only through the sound
-- e-graph path kernel above.
------------------------------------------------------------------------

data IntegerLayerNormExpression : Set where
  rawIntegerLayerNorm :
    ℕ → List C.IntCode → IntegerLayerNormExpression
  centeredIntegerLayerNorm :
    ℕ → List C.IntCode → IntegerLayerNormExpression
  radicandIntegerLayerNorm :
    ℕ → List C.IntCode → IntegerLayerNormExpression

record IntegerLayerNormSemanticState : Set where
  constructor integerLayerNormSemanticState
  field
    epsilon : ℕ
    input : List C.IntCode
    centered : List Int
    radicand : Int
open IntegerLayerNormSemanticState public

integerLayerNormSemanticInterpret :
  IntegerLayerNormExpression →
  IntegerLayerNormSemanticState
integerLayerNormSemanticInterpret
  (rawIntegerLayerNorm epsilon xs) =
  integerLayerNormSemanticState
    epsilon
    xs
    (C.integerLayerNormCenteredNumerators xs)
    (C.integerLayerNormRadicand xs epsilon)
integerLayerNormSemanticInterpret
  (centeredIntegerLayerNorm epsilon xs) =
  integerLayerNormSemanticState
    epsilon
    xs
    (C.integerLayerNormCenteredNumerators xs)
    (C.integerLayerNormRadicand xs epsilon)
integerLayerNormSemanticInterpret
  (radicandIntegerLayerNorm epsilon xs) =
  integerLayerNormSemanticState
    epsilon
    xs
    (C.integerLayerNormCenteredNumerators xs)
    (C.integerLayerNormRadicand xs epsilon)

integerLayerNormRelated :
  IntegerLayerNormExpression →
  IntegerLayerNormExpression →
  Set
integerLayerNormRelated e f =
  integerLayerNormSemanticInterpret e ＝
  integerLayerNormSemanticInterpret f

integerLayerNormRelated-refl :
  ∀ e → integerLayerNormRelated e e
integerLayerNormRelated-refl e = refl

integerLayerNormRelated-sym :
  ∀ {e f} →
  integerLayerNormRelated e f →
  integerLayerNormRelated f e
integerLayerNormRelated-sym = sym

integerLayerNormRelated-trans :
  ∀ {e f g} →
  integerLayerNormRelated e f →
  integerLayerNormRelated f g →
  integerLayerNormRelated e g
integerLayerNormRelated-trans = trans

integerLayerNormEGraphCongruence :
  EGraphCongruence IntegerLayerNormExpression
integerLayerNormEGraphCongruence =
  eGraphCongruence
    integerLayerNormRelated
    integerLayerNormRelated-refl
    integerLayerNormRelated-sym
    integerLayerNormRelated-trans

integerLayerNormEGraphSemantics :
  EGraphSemanticInterpretation
    IntegerLayerNormExpression
    IntegerLayerNormSemanticState
integerLayerNormEGraphSemantics =
  eGraphSemanticInterpretation
    integerLayerNormEGraphCongruence
    integerLayerNormSemanticInterpret
    (λ eq → eq)

integerLayerNormAStarCostModel :
  AStarCostModel IntegerLayerNormExpression
integerLayerNormAStarCostModel =
  aStarCostModel
    (λ _ _ → succ zero)
    (λ _ → zero)

integerLayerNormAStarClosure :
  AStarSemanticClosure
    IntegerLayerNormExpression
    IntegerLayerNormSemanticState
integerLayerNormAStarClosure =
  aStarSemanticClosure
    integerLayerNormEGraphSemantics
    integerLayerNormAStarCostModel

integerLayerNorm-raw-centered-edge :
  ∀ (epsilon : ℕ) (xs : List C.IntCode) →
  CertifiedEGraphEdge
    integerLayerNormEGraphSemantics
    (rawIntegerLayerNorm epsilon xs)
    (centeredIntegerLayerNorm epsilon xs)
integerLayerNorm-raw-centered-edge epsilon xs =
  certifiedEGraphEdge
    (semanticEdgeMetadata
      "integer-layernorm-raw"
      "integer-layernorm-centered"
      "integerLayerNorm-raw-centered-edge"
      []
      semanticProved
      kernelProof
      true)
    (path-step refl (path-refl
      (centeredIntegerLayerNorm epsilon xs)))

integerLayerNorm-centered-radicand-edge :
  ∀ (epsilon : ℕ) (xs : List C.IntCode) →
  CertifiedEGraphEdge
    integerLayerNormEGraphSemantics
    (centeredIntegerLayerNorm epsilon xs)
    (radicandIntegerLayerNorm epsilon xs)
integerLayerNorm-centered-radicand-edge epsilon xs =
  certifiedEGraphEdge
    (semanticEdgeMetadata
      "integer-layernorm-centered"
      "integer-layernorm-radicand"
      "integerLayerNorm-centered-radicand-edge"
      []
      semanticProved
      kernelProof
      true)
    (path-step refl (path-refl
      (radicandIntegerLayerNorm epsilon xs)))

integerLayerNorm-raw-radicand-path :
  ∀ (epsilon : ℕ) (xs : List C.IntCode) →
  EGraphSemanticPath
    (semantics integerLayerNormAStarClosure)
    (rawIntegerLayerNorm epsilon xs)
    (radicandIntegerLayerNorm epsilon xs)
integerLayerNorm-raw-radicand-path epsilon xs =
  eGraph-path-trans
    (path (integerLayerNorm-raw-centered-edge epsilon xs))
    (path (integerLayerNorm-centered-radicand-edge epsilon xs))

integerLayerNorm-a-star-semantic-closure :
  ∀ (epsilon : ℕ) (xs : List C.IntCode) →
  interpret (semantics integerLayerNormAStarClosure)
    (rawIntegerLayerNorm epsilon xs)
  ＝
  interpret (semantics integerLayerNormAStarClosure)
    (radicandIntegerLayerNorm epsilon xs)
integerLayerNorm-a-star-semantic-closure epsilon xs =
  aStar-guided-semantic-closure
    integerLayerNormAStarClosure
    (integerLayerNorm-raw-radicand-path epsilon xs)

record CanonicalIntegerLayerNormEGraphAStarTheorem : Set₁ where
  constructor canonicalIntegerLayerNormEGraphAStarTheorem
  field
    closure :
      AStarSemanticClosure
        IntegerLayerNormExpression
        IntegerLayerNormSemanticState
    planMonoid :
      AStarPlanMonoidTheorem
        IntegerLayerNormExpression
    rawCentered :
      ∀ (epsilon : ℕ) (xs : List C.IntCode) →
      CertifiedEGraphEdge
        integerLayerNormEGraphSemantics
        (rawIntegerLayerNorm epsilon xs)
        (centeredIntegerLayerNorm epsilon xs)
    centeredRadicand :
      ∀ (epsilon : ℕ) (xs : List C.IntCode) →
      CertifiedEGraphEdge
        integerLayerNormEGraphSemantics
        (centeredIntegerLayerNorm epsilon xs)
        (radicandIntegerLayerNorm epsilon xs)
    rawRadicand :
      ∀ (epsilon : ℕ) (xs : List C.IntCode) →
      EGraphSemanticPath
        (semantics integerLayerNormAStarClosure)
        (rawIntegerLayerNorm epsilon xs)
        (radicandIntegerLayerNorm epsilon xs)
    soundPath :
      ∀ (epsilon : ℕ) (xs : List C.IntCode) →
      interpret (semantics integerLayerNormAStarClosure)
        (rawIntegerLayerNorm epsilon xs)
      ＝
      interpret (semantics integerLayerNormAStarClosure)
        (radicandIntegerLayerNorm epsilon xs)

canonical-integer-layernorm-egraph-astar-theorem :
  CanonicalIntegerLayerNormEGraphAStarTheorem
canonical-integer-layernorm-egraph-astar-theorem =
  canonicalIntegerLayerNormEGraphAStarTheorem
    integerLayerNormAStarClosure
    aStar-plan-monoid-theorem IntegerLayerNormExpression
    integerLayerNorm-raw-centered-edge
    integerLayerNorm-centered-radicand-edge
    integerLayerNorm-raw-radicand-path
    integerLayerNorm-a-star-semantic-closure

------------------------------------------------------------------------
-- Concrete finite-rank A* normalization witness.
--
-- This is the first concrete instantiation of the generic
-- EGraphAStarFiniteRankConvergenceWitness. The state is deliberately a
-- three-phase normalization plan rather than the whole learner state:
--
--   raw -> centered -> radicand
--
-- The ℕ rank counts the remaining normalization phases. A* remains the
-- cost-guidance carrier; semantic equality still comes from the e-graph
-- interpretation. The resulting stable phase is persistent for every
-- horizon, giving an explicit infinite stable tail.
------------------------------------------------------------------------

data IntegerLayerNormAStarPhase : Set where
  integerLayerNormRawPhase :
    IntegerLayerNormAStarPhase
  integerLayerNormCenteredPhase :
    IntegerLayerNormAStarPhase
  integerLayerNormRadicandPhase :
    IntegerLayerNormAStarPhase

integerLayerNormAStarStep :
  IntegerLayerNormAStarPhase →
  IntegerLayerNormAStarPhase
integerLayerNormAStarStep integerLayerNormRawPhase =
  integerLayerNormCenteredPhase
integerLayerNormAStarStep integerLayerNormCenteredPhase =
  integerLayerNormRadicandPhase
integerLayerNormAStarStep integerLayerNormRadicandPhase =
  integerLayerNormRadicandPhase

integerLayerNormAStarCandidate :
  ∀ (epsilon : ℕ) (xs : List C.IntCode) →
  IntegerLayerNormAStarPhase →
  IntegerLayerNormExpression
integerLayerNormAStarCandidate epsilon xs
  integerLayerNormRawPhase =
  rawIntegerLayerNorm epsilon xs
integerLayerNormAStarCandidate epsilon xs
  integerLayerNormCenteredPhase =
  centeredIntegerLayerNorm epsilon xs
integerLayerNormAStarCandidate epsilon xs
  integerLayerNormRadicandPhase =
  radicandIntegerLayerNorm epsilon xs

integerLayerNormAStarRank :
  IntegerLayerNormAStarPhase →
  ℕ
integerLayerNormAStarRank integerLayerNormRawPhase =
  succ (succ zero)
integerLayerNormAStarRank integerLayerNormCenteredPhase =
  succ zero
integerLayerNormAStarRank integerLayerNormRadicandPhase =
  zero

integerLayerNormAStarStable :
  IntegerLayerNormAStarPhase →
  Set
integerLayerNormAStarStable phase =
  phase ＝ integerLayerNormRadicandPhase

integerLayerNormAStarRankZero :
  ∀ phase →
  integerLayerNormAStarRank phase ＝ zero →
  integerLayerNormAStarStable phase
integerLayerNormAStarRankZero integerLayerNormRawPhase ()
integerLayerNormAStarRankZero integerLayerNormCenteredPhase ()
integerLayerNormAStarRankZero integerLayerNormRadicandPhase refl =
  refl

integerLayerNorm-absurd :
  ∀ {A : Set} →
  ⊥ →
  A
integerLayerNorm-absurd ()

integerLayerNormAStarStrictDescent :
  ∀ phase →
  ¬ integerLayerNormAStarStable phase →
  integerLayerNormAStarRank
    (integerLayerNormAStarStep phase)
  <
  integerLayerNormAStarRank phase
integerLayerNormAStarStrictDescent
  integerLayerNormRawPhase
  _ =
  <-succ _
integerLayerNormAStarStrictDescent
  integerLayerNormCenteredPhase
  _ =
  <-succ _
integerLayerNormAStarStrictDescent
  integerLayerNormRadicandPhase
  notStable =
  integerLayerNorm-absurd
    (notStable refl)

integerLayerNormAStarStableNext :
  ∀ phase →
  integerLayerNormAStarStable phase →
  integerLayerNormAStarStable
    (integerLayerNormAStarStep phase)
integerLayerNormAStarStableNext
  integerLayerNormRawPhase
  ()
integerLayerNormAStarStableNext
  integerLayerNormCenteredPhase
  ()
integerLayerNormAStarStableNext
  integerLayerNormRadicandPhase
  refl =
  refl

integerLayerNormAStarEventualStable :
  ∀ phase →
  Σ ℕ
    (λ n →
      integerLayerNormAStarStable
        (eGraphAStarIterate
          integerLayerNormAStarStep
          n
          phase))
integerLayerNormAStarEventualStable
  integerLayerNormRawPhase =
  succ (succ zero) , refl
integerLayerNormAStarEventualStable
  integerLayerNormCenteredPhase =
  succ zero , refl
integerLayerNormAStarEventualStable
  integerLayerNormRadicandPhase =
  zero , refl

integerLayerNormAStarStablePath :
  ∀ {epsilon : ℕ} {xs : List C.IntCode} {phase} →
  integerLayerNormAStarStable phase →
  EGraphSemanticPath
    (semantics integerLayerNormAStarClosure)
    (integerLayerNormAStarCandidate epsilon xs phase)
    (radicandIntegerLayerNorm epsilon xs)
integerLayerNormAStarStablePath
  {phase = integerLayerNormRawPhase}
  ()
integerLayerNormAStarStablePath
  {phase = integerLayerNormCenteredPhase}
  ()
integerLayerNormAStarStablePath
  {phase = integerLayerNormRadicandPhase}
  refl =
  path-refl
    (radicandIntegerLayerNorm _ _)

integerLayerNorm-egraph-astar-finite-rank-witness :
  ∀ (epsilon : ℕ) (xs : List C.IntCode) →
  EGraphAStarFiniteRankConvergenceWitness
    IntegerLayerNormExpression
    IntegerLayerNormAStarPhase
integerLayerNorm-egraph-astar-finite-rank-witness epsilon xs =
  eGraphAStarFiniteRankConvergenceWitness
    integerLayerNormAStarClosure
    integerLayerNormAStarStep
    (integerLayerNormAStarCandidate epsilon xs)
    (radicandIntegerLayerNorm epsilon xs)
    integerLayerNormAStarStable
    integerLayerNormAStarRank
    integerLayerNormAStarRankZero
    integerLayerNormAStarStrictDescent
    integerLayerNormAStarStableNext
    integerLayerNormAStarEventualStable
    integerLayerNormAStarStablePath

integerLayerNorm-egraph-astar-eventual-semantic-closure :
  ∀ (epsilon : ℕ) (xs : List C.IntCode)
  (phase : IntegerLayerNormAStarPhase) →
  Σ ℕ
    (λ n →
      interpret
        (semantics integerLayerNormAStarClosure)
        (integerLayerNormAStarCandidate epsilon xs
          (eGraphAStarIterate
            integerLayerNormAStarStep
            n
            phase))
      ＝
      interpret
        (semantics integerLayerNormAStarClosure)
        (radicandIntegerLayerNorm epsilon xs))
integerLayerNorm-egraph-astar-eventual-semantic-closure
  epsilon xs phase =
  eGraphAStarConvergenceSemanticClosure
    (integerLayerNorm-egraph-astar-finite-rank-witness epsilon xs)
    phase

integerLayerNorm-egraph-astar-infinite-stable-tail :
  ∀ (epsilon : ℕ) (xs : List C.IntCode)
  (phase : IntegerLayerNormAStarPhase) →
  Σ ℕ
    (λ n →
      ∀ k →
      integerLayerNormAStarStable
        (eGraphAStarIterate
          integerLayerNormAStarStep
          k
          (eGraphAStarIterate
            integerLayerNormAStarStep
            n
            phase)))
integerLayerNorm-egraph-astar-infinite-stable-tail
  epsilon xs phase
  with integerLayerNormAStarEventualStable phase
... | n , stableAtN =
  n ,
  eGraphAStarStablePathPersists
    (integerLayerNorm-egraph-astar-finite-rank-witness epsilon xs)
    stableAtN

record CanonicalIntegerLayerNormEGraphAStarInfiniteHorizonStabilityTheorem : Set₁ where
  constructor canonicalIntegerLayerNormEGraphAStarInfiniteHorizonStabilityTheorem
  field
    finiteRankWitness :
      ∀ (epsilon : ℕ) (xs : List C.IntCode) →
      EGraphAStarFiniteRankConvergenceWitness
        IntegerLayerNormExpression
        IntegerLayerNormAStarPhase
    eventualSemanticClosure :
      ∀ (epsilon : ℕ) (xs : List C.IntCode)
      (phase : IntegerLayerNormAStarPhase) →
      Σ ℕ
        (λ n →
          interpret
            (semantics integerLayerNormAStarClosure)
            (integerLayerNormAStarCandidate epsilon xs
              (eGraphAStarIterate
                integerLayerNormAStarStep
                n
                phase))
          ＝
          interpret
            (semantics integerLayerNormAStarClosure)
            (radicandIntegerLayerNorm epsilon xs))
    infiniteStableTail :
      ∀ (epsilon : ℕ) (xs : List C.IntCode)
      (phase : IntegerLayerNormAStarPhase) →
      Σ ℕ
        (λ n →
          ∀ k →
          integerLayerNormAStarStable
            (eGraphAStarIterate
              integerLayerNormAStarStep
              k
              (eGraphAStarIterate
                integerLayerNormAStarStep
                n
                phase)))

canonical-integer-layernorm-egraph-astar-infinite-horizon-stability-theorem :
  CanonicalIntegerLayerNormEGraphAStarInfiniteHorizonStabilityTheorem
canonical-integer-layernorm-egraph-astar-infinite-horizon-stability-theorem =
  canonicalIntegerLayerNormEGraphAStarInfiniteHorizonStabilityTheorem
    integerLayerNorm-egraph-astar-finite-rank-witness
    integerLayerNorm-egraph-astar-eventual-semantic-closure
    integerLayerNorm-egraph-astar-infinite-stable-tail


------------------------------------------------------------------------
-- Interpolated execution bridge.
--
-- Agda owns the dependency graph, proof term, semantic search, and extraction.
-- The semantic result is stronger than mere eventual convergence: every
-- element of the infinite stable tail is semantically equal to the exact
-- radicand target. The monadic/Haskell surface and plan monoid remain typed
-- execution carriers, never semantic evidence.
------------------------------------------------------------------------

record CanonicalIntegerLayerNormAStarExecutionBridgeTheorem : Set₁ where
  constructor canonicalIntegerLayerNormAStarExecutionBridgeTheorem
  field
    stableSemanticTail :
      ∀ (epsilon : ℕ) (xs : List C.IntCode)
      (phase : IntegerLayerNormAStarPhase) →
      Σ ℕ
        (λ n →
          ∀ k →
          interpret
            (semantics integerLayerNormAStarClosure)
            (integerLayerNormAStarCandidate epsilon xs
              (eGraphAStarIterate
                integerLayerNormAStarStep
                k
                (eGraphAStarIterate
                  integerLayerNormAStarStep
                  n
                  phase)))
          ＝
          interpret
            (semantics integerLayerNormAStarClosure)
            (radicandIntegerLayerNorm epsilon xs))
    planMonoid :
      AStarPlanMonoidTheorem IntegerLayerNormExpression
    executionMonad :
      AStarHaskellMonadSurface IntegerLayerNormExpression

canonical-integer-layernorm-astar-execution-bridge-theorem :
  CanonicalIntegerLayerNormAStarExecutionBridgeTheorem
canonical-integer-layernorm-astar-execution-bridge-theorem =
  canonicalIntegerLayerNormAStarExecutionBridgeTheorem
    stableSemanticTail
    (aStar-plan-monoid-theorem IntegerLayerNormExpression)
    (aStar-haskell-monad-surface IntegerLayerNormExpression)
  where
  stableSemanticTail :
    ∀ (epsilon : ℕ) (xs : List C.IntCode)
    (phase : IntegerLayerNormAStarPhase) →
    Σ ℕ
      (λ n →
        ∀ k →
        interpret
          (semantics integerLayerNormAStarClosure)
          (integerLayerNormAStarCandidate epsilon xs
            (eGraphAStarIterate
              integerLayerNormAStarStep
              k
              (eGraphAStarIterate
                integerLayerNormAStarStep
                n
                phase)))
        ＝
        interpret
          (semantics integerLayerNormAStarClosure)
          (radicandIntegerLayerNorm epsilon xs))
  stableSemanticTail epsilon xs phase
    with integerLayerNorm-egraph-astar-infinite-stable-tail
      epsilon xs phase
  ... | n , stableTail =
    n ,
    λ k →
      eGraph-path-sound
        integerLayerNormEGraphSemantics
        (integerLayerNormAStarStablePath (stableTail k))

------------------------------------------------------------------------
-- LayerNorm-specific stability and growth, deliberately separate from the
-- retired NormPair replacement theory and from the F4 optimizer growth ray.
--
-- Stability here means that the normalization statistics / denominator
-- interface is unaffected by output-affine configuration changes, while
-- epsilon growth is a separate one-parameter arithmetic ray of the
-- LayerNorm radicand. Neither theorem transports the old NormPair state
-- replacement laws into the new LayerNorm surface.
------------------------------------------------------------------------

nat-ring-solver-layernorm-contribution :
  ∀ (xs : List C.IntCode) (epsilon : ℕ) →
  (succ epsilon ℕ* length xs ℕ* length xs)
  ＝
  (epsilon ℕ* length xs ℕ* length xs)
  + (length xs ℕ* length xs)
nat-ring-solver-layernorm-contribution xs epsilon =
  let n = length xs in
  (succ epsilon ℕ* n) ℕ* n
    ＝⟨ ap (_ℕ* n) (NatMult.mult-commutativity (succ epsilon) n) ⟩
  (n ℕ* succ epsilon) ℕ* n
    ＝⟨ refl ⟩
  (n + n ℕ* epsilon) ℕ* n
    ＝⟨ NatMult.distributivity-mult-over-addition' n (n ℕ* epsilon) n ⟩
  (n ℕ* n) + (n ℕ* epsilon) ℕ* n
    ＝⟨ ap ((n ℕ* n) +_) (NatMult.mult-associativity n epsilon n) ⟩
  (n ℕ* n) + n ℕ* (epsilon ℕ* n)
    ＝⟨ ap ((n ℕ* n) +_) (NatMult.mult-commutativity n (epsilon ℕ* n)) ⟩
  (n ℕ* n) + (epsilon ℕ* n) ℕ* n
    ＝⟨ addition-commutativity (n ℕ* n) ((epsilon ℕ* n) ℕ* n) ⟩
  (epsilon ℕ* n) ℕ* n + (n ℕ* n) ∎

integerLayerNorm-epsilon-contribution-succ :
  ∀ (xs : List C.IntCode) (epsilon : ℕ) →
  (succ epsilon * length xs * length xs)
  ＝
  (epsilon * length xs * length xs)
  + (length xs * length xs)
integerLayerNorm-epsilon-contribution-succ =
  nat-ring-solver-layernorm-contribution

integerLayerNorm-radicand-epsilon-zero :
  ∀ (xs : List C.IntCode) →
  C.integerLayerNormRadicand xs zero
  ＝
  C.integerLayerNormVarianceNumerator xs
integerLayerNorm-radicand-epsilon-zero xs = refl

integerLayerNorm-radicand-epsilon-succ :
  ∀ (xs : List C.IntCode) (epsilon : ℕ) →
  C.integerLayerNormRadicand xs (succ epsilon)
  ＝
  C.integerLayerNormRadicand xs epsilon
  +Int
  (pos (length xs * length xs))
integerLayerNorm-radicand-epsilon-succ xs epsilon =
  trans
    (ap
      (λ n →
        C.integerLayerNormVarianceNumerator xs
        +Int
        (pos n))
      (integerLayerNorm-epsilon-contribution-succ xs epsilon))
    (sym
      (integer-ring-solver-assoc
        (C.integerLayerNormVarianceNumerator xs)
        (pos (epsilon * length xs * length xs))
        (pos (length xs * length xs))))

record IntegerLayerNormConfigurationStabilityTheorem : Set₁ where
  constructor integerLayerNormConfigurationStabilityTheorem
  field
    eGraphAStar :
      CanonicalIntegerLayerNormEGraphAStarTheorem
    centeredStatisticsIndependentOfEpsilon :
      ∀ (xs : List C.IntCode) (epsilon delta : ℕ) →
      centered
        (integerLayerNormSemanticInterpret
          (rawIntegerLayerNorm epsilon xs))
      ＝
      centered
        (integerLayerNormSemanticInterpret
          (rawIntegerLayerNorm delta xs))
    denominatorConfigurationStable :
      ∀ (xs : List C.IntCode)
      (config₁ config₂ : C.IntegerLayerNormConfig)
      (certificate : C.IntegerLayerNormCertificate xs)
      (x : C.IntCode) →
      C.denominator
        (C.integerLayerNormValue config₁ certificate x)
      ＝
      C.denominator
        (C.integerLayerNormValue config₂ certificate x)

open IntegerLayerNormConfigurationStabilityTheorem public

integer-layernorm-centered-statistics-independent-of-epsilon :
  ∀ (xs : List C.IntCode) (epsilon delta : ℕ) →
  centered
    (integerLayerNormSemanticInterpret
      (rawIntegerLayerNorm epsilon xs))
  ＝
  centered
    (integerLayerNormSemanticInterpret
      (rawIntegerLayerNorm delta xs))
integer-layernorm-centered-statistics-independent-of-epsilon _ _ _ = refl

integer-layernorm-denominator-configuration-stable :
  ∀ (xs : List C.IntCode)
  (config₁ config₂ : C.IntegerLayerNormConfig)
  (certificate : C.IntegerLayerNormCertificate xs)
  (x : C.IntCode) →
  C.denominator
    (C.integerLayerNormValue config₁ certificate x)
  ＝
  C.denominator
    (C.integerLayerNormValue config₂ certificate x)
integer-layernorm-denominator-configuration-stable
  _ _ _ certificate x = refl

integer-layernorm-configuration-stability-theorem :
  IntegerLayerNormConfigurationStabilityTheorem
integer-layernorm-configuration-stability-theorem =
  integerLayerNormConfigurationStabilityTheorem
    canonical-integer-layernorm-egraph-astar-theorem
    integer-layernorm-centered-statistics-independent-of-epsilon
    integer-layernorm-denominator-configuration-stable

integerLayerNorm-radicand-epsilon-linear :
  ∀ (xs : List C.IntCode) (epsilon : ℕ) →
  C.integerLayerNormRadicand xs epsilon
  ＝
  C.integerLayerNormVarianceNumerator xs
  +Int
  (pos (epsilon * length xs * length xs))
integerLayerNorm-radicand-epsilon-linear xs zero =
  trans
    (integerLayerNorm-radicand-epsilon-zero xs)
    (sym
      (ℤ-zero-right-neutral
        (C.integerLayerNormVarianceNumerator xs)))
integerLayerNorm-radicand-epsilon-linear xs (succ epsilon) =
  trans
    (integerLayerNorm-radicand-epsilon-succ xs epsilon)
    (trans
      (cong₂ _+Int_
        (integerLayerNorm-radicand-epsilon-linear xs epsilon)
        refl)
      (trans
        (sym
          (ℤ+-assoc
            (C.integerLayerNormVarianceNumerator xs)
            (pos (epsilon * length xs * length xs))
            (pos (length xs * length xs))))
        (ap
          (λ n →
            C.integerLayerNormVarianceNumerator xs
            +Int
            (pos n))
          (sym
            (integerLayerNorm-epsilon-contribution-succ
              xs
              epsilon)))))

record IntegerLayerNormEpsilonRayGrowthTheorem : Set₁ where
  constructor integerLayerNormEpsilonRayGrowthTheorem
  field
    eGraphAStar :
      CanonicalIntegerLayerNormEGraphAStarTheorem
    zeroRay :
      ∀ (xs : List C.IntCode) →
      C.integerLayerNormRadicand xs zero
      ＝
      C.integerLayerNormVarianceNumerator xs
    successorRay :
      ∀ (xs : List C.IntCode) (epsilon : ℕ) →
      C.integerLayerNormRadicand xs (succ epsilon)
      ＝
      C.integerLayerNormRadicand xs epsilon
      +Int
      (pos (length xs * length xs))
    linearRay :
      ∀ (xs : List C.IntCode) (epsilon : ℕ) →
      C.integerLayerNormRadicand xs epsilon
      ＝
      C.integerLayerNormVarianceNumerator xs
      +Int
      (pos (epsilon * length xs * length xs))

open IntegerLayerNormEpsilonRayGrowthTheorem public

integer-layernorm-epsilon-ray-growth-theorem :
  IntegerLayerNormEpsilonRayGrowthTheorem
integer-layernorm-epsilon-ray-growth-theorem =
  integerLayerNormEpsilonRayGrowthTheorem
    canonical-integer-layernorm-egraph-astar-theorem
    integerLayerNorm-radicand-epsilon-zero
    integerLayerNorm-radicand-epsilon-succ
    integerLayerNorm-radicand-epsilon-linear

record CanonicalIntegerLayerNormStabilityGrowthTheorem : Set₁ where
  constructor canonicalIntegerLayerNormStabilityGrowthTheorem
  field
    configurationStability :
      IntegerLayerNormConfigurationStabilityTheorem
    epsilonRayGrowth :
      IntegerLayerNormEpsilonRayGrowthTheorem

open CanonicalIntegerLayerNormStabilityGrowthTheorem public

canonical-integer-layernorm-stability-growth-theorem :
  CanonicalIntegerLayerNormStabilityGrowthTheorem
canonical-integer-layernorm-stability-growth-theorem =
  canonicalIntegerLayerNormStabilityGrowthTheorem
    integer-layernorm-configuration-stability-theorem
    integer-layernorm-epsilon-ray-growth-theorem

record CanonicalF4GlobalOptimizerStabilityTheorem : Set₁ where
  constructor canonicalF4GlobalOptimizerStabilityTheorem
  field
    thetaTranslation :
      ∀ {A} (K : C.FullLearnerKernel A) (s : C.FullLearnerState A) →
      C.thetaQ (C.canonicalOptimizerStep K s) ＝
      C.intCodeAdd
        (C.intCodeAdd (C.thetaQ (C.optimizer s)) (C.canonicalSignal K s))
        (C.l2Correction (C.globalL2 (C.optimizerKernel K)))
    stableNonThetaCoordinates :
      ∀ {A} (K : C.FullLearnerKernel A) (s : C.FullLearnerState A) →
      (C.rTheta (C.canonicalOptimizerStep K s) ＝ C.zeroIntCode) ×
      (C.eQ (C.canonicalOptimizerStep K s) ＝ C.eQ (C.optimizer s)) ×
      (C.rE (C.canonicalOptimizerStep K s) ＝ C.rE (C.optimizer s)) ×
      (C.rL (C.canonicalOptimizerStep K s) ＝ C.rL (C.optimizer s))
    equalInputStability :
      ∀ {A} (K : C.FullLearnerKernel A)
        (s t : C.FullLearnerState A) →
      C.optimizer s ＝ C.optimizer t →
      C.canonicalSignal K s ＝ C.canonicalSignal K t →
      C.canonicalOptimizerStep K s ＝ C.canonicalOptimizerStep K t

open CanonicalF4GlobalOptimizerStabilityTheorem public

canonical-f4-global-optimizer-stability-theorem :
  CanonicalF4GlobalOptimizerStabilityTheorem
canonical-f4-global-optimizer-stability-theorem =
  canonicalF4GlobalOptimizerStabilityTheorem
    (λ K s → C.f4ParameterInvariant
      (C.optimizerKernel K) (C.optimizer s) (C.canonicalSignal K s))
    (λ K s → refl , (refl , (refl , refl)))
    (λ K s t optimizerEq signalEq →
      cong₂
        (λ optimizer signal →
          C.f4ThetaStep (C.optimizerKernel K) optimizer signal)
        optimizerEq signalEq)

record CanonicalF4IntegerLayerNormStabilityBoundaryTheorem : Set₁ where
  constructor canonicalF4IntegerLayerNormStabilityBoundaryTheorem
  field
    f4OptimizerStability :
      CanonicalF4GlobalOptimizerStabilityTheorem
    layerNormStabilityGrowth :
      CanonicalIntegerLayerNormStabilityGrowthTheorem

open CanonicalF4IntegerLayerNormStabilityBoundaryTheorem public

canonical-f4-integer-layernorm-stability-boundary-theorem :
  CanonicalF4IntegerLayerNormStabilityBoundaryTheorem
canonical-f4-integer-layernorm-stability-boundary-theorem =
  canonicalF4IntegerLayerNormStabilityBoundaryTheorem
    canonical-f4-global-optimizer-stability-theorem
    canonical-integer-layernorm-stability-growth-theorem

------------------------------------------------------------------------
-- The F4 and LayerNorm stability families share the theorem monolith but
-- remain separate typed carriers. This boundary does not recreate a
-- NormPair replacement operation or assert that F4 optimizer forcing
-- changes LayerNorm statistics/configuration.

------------------------------------------------------------------------
-- The theorem is unconditional over the complete surviving Agda-file
-- index and any supplied semantic family:
--
--   enumerated file
--     -> supplied sound interpretation
--     -> sound e-graph path
--     -> exact endpoint equality
--
-- A* costs/heuristics guide discovery but are not equality evidence.
-- This does not assert that every physical Maxwell witness, economic
-- equilibrium witness, or other domain-specific inhabitant exists.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Canonical theorem section: four-law closure witnesses.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Minimal typed contract for the missing four-law closure witnesses.
--
-- This module is intentionally a contract, not an existence theorem.
-- It records exactly the semantic data that must be inhabited before
-- Law I + Law III + physics-to-learner transport can be promoted into
-- the existing Law II/Law IV composition.
------------------------------------------------------------------------


record LawIPhysicsWitness
  (LearnerState PhysicalState Current : Set) : Set₁ where
  constructor lawIPhysicsWitness
  field
    encode : LearnerState → PhysicalState
    decode : PhysicalState → LearnerState
    decodeEncode :
      ∀ s → decode (encode s) ＝ s
    trajectory :
      PhysicalState → PhysicalState
    current :
      PhysicalState → Current
    trajectoryCurrentCompatibility :
      ∀ p → current (trajectory p) ＝ current p

record LawIIIVariationalWitness
  (LearnerState PhysicalState Variation Action : Set)
  (Admissible : Variation → Set)
  (Stationary : PhysicalState → Set) : Set₁ where
  constructor lawIIIVariationalWitness
  field
    encode : LearnerState → PhysicalState
    decode : PhysicalState → LearnerState
    decodeEncode :
      ∀ s → decode (encode s) ＝ s
    variation : PhysicalState → Variation
    action : PhysicalState → Action
    admissibleVariation :
      ∀ p → Admissible (variation p)
    stationary :
      ∀ p → Stationary p

record PhysicsToLearnerTransitionWitness
  (LearnerState PhysicalState : Set)
  (learnerStep : LearnerState → LearnerState)
  (physicalStep : PhysicalState → PhysicalState) : Set₁ where
  constructor physicsToLearnerTransitionWitness
  field
    encode : LearnerState → PhysicalState
    decode : PhysicalState → LearnerState
    decodeEncode :
      ∀ s → decode (encode s) ＝ s
    stepConjugacy :
      ∀ s →
      encode (learnerStep s)
      ＝
      physicalStep (encode s)

record FourLawOneStepWitnessContract
  (LearnerState PhysicalState Current Variation Action : Set)
  (Admissible : Variation → Set)
  (Stationary : PhysicalState → Set)
  (learnerStep : LearnerState → LearnerState)
  (physicalStep : PhysicalState → PhysicalState) : Set₁ where
  constructor fourLawOneStepWitnessContract
  field
    lawI :
      LawIPhysicsWitness
        LearnerState
        PhysicalState
        Current
    lawIII :
      LawIIIVariationalWitness
        LearnerState
        PhysicalState
        Variation
        Action
        Admissible
        Stationary
    physicsToLearner :
      PhysicsToLearnerTransitionWitness
        LearnerState
        PhysicalState
        learnerStep
        physicalStep

------------------------------------------------------------------------
-- Generic autonomous-time lifting of the physics-to-learner square.
-- This is proof infrastructure only; it does not create a missing
-- physics witness.
------------------------------------------------------------------------

iterateConjugacy :
  ∀ {LearnerState PhysicalState : Set}
  {learnerStep : LearnerState → LearnerState}
  {physicalStep : PhysicalState → PhysicalState}
  (encode : LearnerState → PhysicalState)
  (stepConjugacy :
    ∀ s →
    encode (learnerStep s) ＝
    physicalStep (encode s)) →
  ∀ n s →
  encode (C.iterate learnerStep n s)
  ＝
  C.iterate physicalStep n (encode s)
iterateConjugacy encode stepConjugacy zero s = refl
iterateConjugacy {learnerStep = learnerStep} {physicalStep = physicalStep} encode stepConjugacy (succ n) s =
  trans
    (stepConjugacy (C.iterate learnerStep n s))
    (ap
      physicalStep
      (iterateConjugacy encode stepConjugacy n s))

------------------------------------------------------------------------
-- Input-indexed square contract for prefix scans. This is deliberately
-- separate from the autonomous iterate witness: a prefix consumes an
-- input at every step, so the commuting law must quantify over input.
------------------------------------------------------------------------

record InputIndexedConjugacy
  (LearnerState PhysicalState Input : Set) : Set₁ where
  constructor inputIndexedConjugacy
  field
    encode : LearnerState → PhysicalState
    learnerStep : LearnerState → Input → LearnerState
    physicalStep : PhysicalState → Input → PhysicalState
    stepConjugacy :
      ∀ s x →
      encode (learnerStep s x)
      ＝
      physicalStep (encode s) x

open InputIndexedConjugacy public

prefixScan :
  ∀ {State Input : Set} →
  (State → Input → State) →
  List Input →
  State →
  State
prefixScan step [] s = s
prefixScan step (x ∷ xs) s =
  prefixScan step xs (step s x)

prefixScanConjugacy :
  ∀ {LearnerState PhysicalState Input : Set}
  (R : InputIndexedConjugacy LearnerState PhysicalState Input) →
  ∀ xs s →
  encode R (prefixScan (learnerStep R) xs s)
  ＝
  prefixScan (physicalStep R) xs (encode R s)
prefixScanConjugacy R [] s = refl
prefixScanConjugacy R (x ∷ xs) s =
  trans
    (prefixScanConjugacy
      R
      xs
      (learnerStep R s x))
    (ap
      (prefixScan (physicalStep R) xs)
      (stepConjugacy R s x))


------------------------------------------------------------------------
-- Canonical recurrent permutation-composition boundary.
--
-- The recurrent scan is associative through MonoidAffine composition,
-- but associativity alone does not imply permutation invariance. The
-- following relation is a small, list-generic permutation presentation;
-- it uses no finite-cardinality encoding and therefore stays independent
-- of a particular finite cardinality.
------------------------------------------------------------------------

data CanonicalListPermutation {A : Set} : List A -> List A -> Set where
  canonical-perm-refl :
    ∀ {xs} →
    CanonicalListPermutation xs xs
  canonical-perm-swap :
    ∀ (x y : A) (xs : List A) →
    CanonicalListPermutation
      (x ∷ y ∷ xs)
      (y ∷ x ∷ xs)
  canonical-perm-cons :
    ∀ {x xs ys} →
    CanonicalListPermutation xs ys →
    CanonicalListPermutation
      (x ∷ xs)
      (x ∷ ys)
  canonical-perm-trans :
    ∀ {xs ys zs} →
    CanonicalListPermutation xs ys →
    CanonicalListPermutation ys zs →
    CanonicalListPermutation xs zs

CanonicalLearnerPermutationInvariant : Set₁
CanonicalLearnerPermutationInvariant =
  ∀ (xs ys : List C.IntCode) →
  CanonicalListPermutation xs ys →
  ∀ c →
  C.runMonoidLSTMCell xs c ＝
  C.runMonoidLSTMCell ys c

canonicalNegativeOne8 : C.IntCode
canonicalNegativeOne8 = C.intCode (negsucc zero)

canonicalPermutation-swap :
  CanonicalListPermutation
    (C.oneIntCode ∷ canonicalNegativeOne8 ∷ [])
    (canonicalNegativeOne8 ∷ C.oneIntCode ∷ [])
canonicalPermutation-swap =
  canonical-perm-swap C.oneIntCode canonicalNegativeOne8 []

canonicalPermutation-left :
  C.runMonoidLSTMCell
    (C.oneIntCode ∷ canonicalNegativeOne8 ∷ [])
    C.zeroIntCode
  ＝
  C.zeroIntCode
canonicalPermutation-left = refl

canonicalPermutation-right :
  C.runMonoidLSTMCell
    (canonicalNegativeOne8 ∷ C.oneIntCode ∷ [])
    C.zeroIntCode
  ＝
  C.oneIntCode
canonicalPermutation-right = refl

canonicalZeroInt-not-oneInt :
  ¬ ((pos 0) ＝ (pos 1))
canonicalZeroInt-not-oneInt ()

canonicalZero8-not-oneIntCode :
  C.zeroIntCode ≢ C.oneIntCode
canonicalZero8-not-oneIntCode eq =
  canonicalZeroInt-not-oneInt
    (C.intCode-code-injective eq)

canonicalPermutation-results-distinct :
  C.runMonoidLSTMCell
    (C.oneIntCode ∷ canonicalNegativeOne8 ∷ [])
    C.zeroIntCode
  ≢
  C.runMonoidLSTMCell
    (canonicalNegativeOne8 ∷ C.oneIntCode ∷ [])
    C.zeroIntCode
canonicalPermutation-results-distinct eq =
  canonicalZero8-not-oneIntCode
    (trans
      (sym canonicalPermutation-left)
      (trans eq canonicalPermutation-right))

canonicalLearnerPermutationInvariant-impossible :
  CanonicalLearnerPermutationInvariant → ⊥
canonicalLearnerPermutationInvariant-impossible invariant =
  canonicalPermutation-results-distinct
    (invariant
      (C.oneIntCode ∷ canonicalNegativeOne8 ∷ [])
      (canonicalNegativeOne8 ∷ C.oneIntCode ∷ [])
      canonicalPermutation-swap
      C.zeroIntCode)

record CanonicalLearnerPermutationCompositionImpossibilityTheorem : Set₁ where
  constructor canonicalLearnerPermutationCompositionImpossibilityTheorem
  field
    permutationWitness :
      CanonicalListPermutation
        (C.oneIntCode ∷ canonicalNegativeOne8 ∷ [])
        (canonicalNegativeOne8 ∷ C.oneIntCode ∷ [])
    distinctResults :
      C.runMonoidLSTMCell
        (C.oneIntCode ∷ canonicalNegativeOne8 ∷ [])
        C.zeroIntCode
      ≢
      C.runMonoidLSTMCell
        (canonicalNegativeOne8 ∷ C.oneIntCode ∷ [])
        C.zeroIntCode
    noGlobalPermutationInvariant :
      CanonicalLearnerPermutationInvariant → ⊥

canonical-learner-permutation-composition-impossibility-theorem :
  CanonicalLearnerPermutationCompositionImpossibilityTheorem
canonical-learner-permutation-composition-impossibility-theorem =
  canonicalLearnerPermutationCompositionImpossibilityTheorem
    canonicalPermutation-swap
    canonicalPermutation-results-distinct
    canonicalLearnerPermutationInvariant-impossible

------------------------------------------------------------------------
-- No inhabitant is supplied here. The admissibility and stationarity
-- predicates are explicit semantic obligations; these contracts do not
-- manufacture them from learner algebra.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Canonical theorem section: four-law closure impossibility boundary.
------------------------------------------------------------------------

GenericFourLawClosureConstructor :
  Set₁
GenericFourLawClosureConstructor =
  ∀ {LearnerState PhysicalState Current Variation Action : Set}
    (Admissible : Variation → Set)
    (Stationary : PhysicalState → Set)
    (learnerStep : LearnerState → LearnerState)
    (physicalStep : PhysicalState → PhysicalState) →
    FourLawOneStepWitnessContract
      LearnerState
      PhysicalState
      Current
      Variation
      Action
      Admissible
      Stationary
      learnerStep
      physicalStep

no-generic-four-law-closure-constructor :
  GenericFourLawClosureConstructor → ⊥
no-generic-four-law-closure-constructor make =
  LawIIIVariationalWitness.stationary
    (FourLawOneStepWitnessContract.lawIII
      (make
        {LearnerState = ⊤}
        {PhysicalState = ⊤}
        {Current = ⊤}
        {Variation = ⊤}
        {Action = ⊤}
        (λ _ → ⊤)
        (λ _ → ⊥)
        (λ _ → tt)
        (λ _ → tt)))
    tt

NoGenericFourLawClosure : Set₁
NoGenericFourLawClosure = GenericFourLawClosureConstructor → ⊥

------------------------------------------------------------------------
-- Canonical theorem section: GRU fractal injective composition.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Generic self-similar/fractal injective-composition kernel.
--
-- "Fractal" is used here only with an explicit level relation and an
-- inter-level transport law. Mere indexing by Level is not treated as
-- fractality.
------------------------------------------------------------------------


record FractalInjectiveComposition
  (Level State Observation : Set)
  (Refines : Level → Level → Set) : Set₁ where
  constructor fractalInjectiveComposition
  field
    encode : Level → State → Observation
    decode : Level → Observation → State
    decodeEncode : ∀ level state → decode level (encode level state) ＝ state

    transportObservation :
      ∀ {lower upper} →
      Refines lower upper →
      Observation →
      Observation

    transportInjective :
      ∀ {lower upper} {r : Refines lower upper} {x y : Observation} →
      transportObservation r x ＝ transportObservation r y →
      x ＝ y

    transportEncode :
      ∀ {lower upper} (r : Refines lower upper) state →
      transportObservation r (encode lower state) ＝
      encode upper state

open FractalInjectiveComposition public

fractalLevelInjective :
  ∀ {Level State Observation : Set}
  {Refines : Level → Level → Set}
  (F : FractalInjectiveComposition Level State Observation Refines) →
  ∀ level {s t : State} →
  encode F level s ＝ encode F level t →
  s ＝ t
fractalLevelInjective F level eq =
  trans
    (decodeEncode F level _)
    (ap (decode F level) eq)

fractalTransportedEncodeInjective :
  ∀ {Level State Observation : Set}
  {Refines : Level → Level → Set}
  (F : FractalInjectiveComposition Level State Observation Refines) →
  ∀ {lower upper} (r : Refines lower upper) {s t : State} →
  transportObservation F r (encode F lower s) ＝
  transportObservation F r (encode F lower t) →
  s ＝ t
fractalTransportedEncodeInjective F {upper = upper} r eq =
  fractalLevelInjective F upper
    (trans
      (transportEncode F r _)
      (trans
        (transportInjective F eq)
        (sym (transportEncode F r _))))

------------------------------------------------------------------------
-- Canonical theorem section: canonical GRU fractal injective composition.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Canonical GRU instantiation of the fractal injective-composition kernel.
--
-- ℕ indexes scale. The relation m ≤ n records refinement from a lower
-- level to an upper level. The canonical statistical observation is reused
-- unchanged at every scale, and the inter-level transport is the identity.
-- This is therefore an explicit scale-invariant self-similar instance,
-- not an assertion that every possible fractal representation is GRU
-- injective.
------------------------------------------------------------------------

GRUFractalLevel : Set
GRUFractalLevel = ℕ

GRUFractalRefines : GRUFractalLevel → GRUFractalLevel → Set
GRUFractalRefines lower upper = lower ≤ upper

canonicalGRUFractal : FractalInjectiveComposition
  GRUFractalLevel
  C.GRUState
  CanonicalGRUStatisticalObservation
  GRUFractalRefines
canonicalGRUFractal =
  fractalInjectiveComposition
    (λ _ → canonicalGRUStatisticalEncode)
    (λ _ → canonicalGRUStatisticalDecode)
    (λ level state → canonicalGRUStatisticalDecodeEncode state)
    (λ _ observation → observation)
    (λ eq → eq)
    (λ _ state → refl)

canonicalGRUFractalLevelInjective :
  ∀ level {s t : C.GRUState} →
  encode canonicalGRUFractal level s ＝
  encode canonicalGRUFractal level t →
  s ＝ t
canonicalGRUFractalLevelInjective =
  fractalLevelInjective canonicalGRUFractal

canonicalGRUFractalTransportedInjective :
  ∀ {lower upper : GRUFractalLevel}
  (r : GRUFractalRefines lower upper)
  {s t : C.GRUState} →
  transportObservation canonicalGRUFractal r
    (encode canonicalGRUFractal lower s) ＝
  transportObservation canonicalGRUFractal r
    (encode canonicalGRUFractal lower t) →
  s ＝ t
canonicalGRUFractalTransportedInjective =
  fractalTransportedEncodeInjective canonicalGRUFractal

canonicalGRUTwoScaleRefinement :
  GRUFractalRefines zero (succ zero)
canonicalGRUTwoScaleRefinement = zero-least (succ zero)

canonicalGRUTwoScaleInjective :
  ∀ {s t : C.GRUState} →
  transportObservation canonicalGRUFractal canonicalGRUTwoScaleRefinement
    (encode canonicalGRUFractal zero s) ＝
  transportObservation canonicalGRUFractal canonicalGRUTwoScaleRefinement
    (encode canonicalGRUFractal zero t) →
  s ＝ t
canonicalGRUTwoScaleInjective =
  canonicalGRUFractalTransportedInjective canonicalGRUTwoScaleRefinement

------------------------------------------------------------------------
-- Canonical theorem section: GRU fractal domain adapters.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Domain adapters for the GRU-injective fractal composition seam.
--
-- These are proof-relevant contracts, not fabricated inhabitants.
-- Physics remains blocked by the concrete Law-I/Law-III witnesses.
-- Economics additionally requires a genuine inter-level transport on
-- the economic carrier, not merely a level index.
------------------------------------------------------------------------

record PhysicsGRUFractalAdapter
  (Level LearnerState PhysicalState Observation Current Variation Action : Set)
  (Refines : Level → Level → Set)
  (Admissible : Variation → Set)
  (Stationary : PhysicalState → Set)
  (learnerStep : LearnerState → LearnerState)
  (physicalStep : PhysicalState → PhysicalState) : Set₁ where
  constructor physicsGRUFractalAdapter
  field
    fourLawWitness :
      FourLawOneStepWitnessContract
        LearnerState
        PhysicalState
        Current
        Variation
        Action
        Admissible
        Stationary
        learnerStep
        physicalStep

    injectiveFractalRepresentation :
      FractalInjectiveComposition
        Level
        LearnerState
        Observation
        Refines

record EconomicsGRUFractalAdapter
  (Level LearnerState EconomicState Observation : Set)
  (Refines : Level → Level → Set)
  (learnerStep : LearnerState → LearnerState)
  (economicStep : EconomicState → EconomicState) : Set₁ where
  constructor economicsGRUFractalAdapter
  field
    learnerToEconomic :
      LearnerState → EconomicState
    economicToLearner :
      EconomicState → LearnerState

    learnerToEconomicInverse :
      ∀ s →
      economicToLearner (learnerToEconomic s) ＝ s

    economicToLearnerInverse :
      ∀ e →
      learnerToEconomic (economicToLearner e) ＝ e

    stepConjugacy :
      ∀ s →
      learnerToEconomic (learnerStep s) ＝
      economicStep (learnerToEconomic s)

    injectiveFractalRepresentation :
      FractalInjectiveComposition
        Level
        LearnerState
        Observation
        Refines

    economicObservation :
      EconomicState → Observation

    economicLevelTransport :
      ∀ {lower upper} →
      Refines lower upper →
      EconomicState →
      EconomicState

    economicLevelTransportInjective :
      ∀ {lower upper}
      {r : Refines lower upper}
      {x y : EconomicState} →
      economicLevelTransport r x ＝
      economicLevelTransport r y →
      x ＝ y

    economicLevelTransportRepresentation :
      ∀ {lower upper}
      (r : Refines lower upper)
      (e : EconomicState) →
      economicObservation
        (economicLevelTransport r e)
      ＝
      FractalInjectiveComposition.transportObservation
        injectiveFractalRepresentation
        r
        (economicObservation e)

open PhysicsGRUFractalAdapter public
open EconomicsGRUFractalAdapter public

------------------------------------------------------------------------
-- Canonical theorem section: GRU fractal limit closure.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Arbitrary-limit closure boundary for GRU-injective fractal composition.
-- A limit object is not assumed to preserve injectivity merely because
-- every finite/indexed approximation is injective.
------------------------------------------------------------------------


record FractalLimitClosure
  (Level State Observation LimitObservation : Set)
  (Refines : Level → Level → Set)
  (encode : Level → State → Observation)
  (limitEncode : State → LimitObservation)
  : Set₁ where
  constructor fractalLimitClosure
  field
    Approx : Observation → LimitObservation → Set
    approximationWitness :
      ∀ level state →
      Approx (encode level state) (limitEncode state)
    limitSeparation :
      ∀ {s t : State} →
      limitEncode s ＝ limitEncode t →
      s ＝ t

open FractalLimitClosure public

fractalLimitInjective :
  ∀ {Level State Observation LimitObservation : Set}
  {Refines : Level → Level → Set}
  {encode : Level → State → Observation}
  {limitEncode : State → LimitObservation}
  (F : FractalLimitClosure
    Level State Observation LimitObservation
    Refines encode limitEncode) →
  ∀ {s t : State} →
  limitEncode s ＝ limitEncode t →
  s ＝ t
fractalLimitInjective F = limitSeparation F

------------------------------------------------------------------------
-- Canonical theorem section: GRU fractal limit decoder survival.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Decoder survival through a fractal limit.
--
-- This module isolates the exact missing seam after finite/indexed GRU
-- injectivity: a compatible family of finite decoders must determine a
-- single decoder on the limit carrier.
--
-- No topological limit or existence claim is manufactured here.
------------------------------------------------------------------------


record CoherentLimitDecoder
  (Level State Observation LimitObservation : Set)
  (encode : Level → State → Observation)
  (limitEncode : State → LimitObservation)
  : Set₁ where
  constructor coherentLimitDecoder
  field
    decode : Level → Observation → State
    limitDecode : LimitObservation → State
    projection : Level → LimitObservation → Observation
    projectionEncode :
      ∀ level state →
      projection level (limitEncode state) ＝ encode level state
    decoderCoherence :
      ∀ level limitObservation →
      decode level (projection level limitObservation) ＝
      limitDecode limitObservation

open CoherentLimitDecoder public

coherentLimitDecoder-left-inverse :
  ∀ {Level State Observation LimitObservation : Set}
  {encode : Level → State → Observation}
  {limitEncode : State → LimitObservation}
  (C :
    CoherentLimitDecoder
      Level State Observation LimitObservation
      encode limitEncode) →
  ∀ level state →
  decode C level (encode level state) ＝ state →
  limitDecode C (limitEncode state) ＝ state
coherentLimitDecoder-left-inverse {limitEncode = limitEncode} C level state finiteLeftInverse =
  trans
    (sym (decoderCoherence C level (limitEncode state)))
    (trans
      (ap (decode C level) (projectionEncode C level state))
      finiteLeftInverse)

------------------------------------------------------------------------
-- The graph edge represented by this module is:
--
--   finite decoder left inverse
--     + limit projection
--     + projection/encoding compatibility
--     + decoder coherence
--     -> limit-surviving left inverse
--
-- Once the resulting limit decoder is available, the existing
-- GRUFractalEGraphAStarLimitComposition module derives limit injectivity.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Canonical theorem section: GRU fractal e-graph/A* limit composition.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- GRU fractal e-graph/A* limit composition.
--
-- The existing repository e-graph/A* layer is discovery/search
-- infrastructure; Agda remains proof-authoritative. This module closes
-- the specific missing implication at the fractal-limit boundary:
--
--   surviving global left inverse
--     -> limit separation
--     -> limit injectivity
--
-- Therefore limit separation is not a second primitive assumption when
-- a decoder survives the limit with a left-inverse law.
------------------------------------------------------------------------


record LimitLeftInverse
  (State LimitObservation : Set)
  (limitEncode : State → LimitObservation)
  : Set₁ where
  constructor limitLeftInverse
  field
    limitDecode : LimitObservation → State
    decodeEncode :
      ∀ state →
      limitDecode (limitEncode state) ＝ state

open LimitLeftInverse public

limitSeparation-from-left-inverse :
  ∀ {State LimitObservation : Set}
  {limitEncode : State → LimitObservation}
  (L : LimitLeftInverse State LimitObservation limitEncode) →
  ∀ {s t : State} →
  limitEncode s ＝ limitEncode t →
  s ＝ t
limitSeparation-from-left-inverse L {s} {t} eq =
  trans
    (sym (decodeEncode L s))
    (trans
      (ap (limitDecode L) eq)
      (decodeEncode L t))

limitInjective-from-left-inverse :
  ∀ {State LimitObservation : Set}
  {limitEncode : State → LimitObservation}
  (L : LimitLeftInverse State LimitObservation limitEncode) →
  ∀ {s t : State} →
  limitEncode s ＝ limitEncode t →
  s ＝ t
limitInjective-from-left-inverse =
  limitSeparation-from-left-inverse

fractalLimitClosure-from-left-inverse :
  ∀ {Level State Observation LimitObservation : Set}
  {Refines : Level → Level → Set}
  {encode : Level → State → Observation}
  {limitEncode : State → LimitObservation}
  (Approx : Observation → LimitObservation → Set)
  (approximationWitness :
    ∀ level state →
    Approx (encode level state) (limitEncode state))
  (L : LimitLeftInverse State LimitObservation limitEncode) →
  FractalLimitClosure
    Level State Observation LimitObservation
    Refines encode limitEncode
fractalLimitClosure-from-left-inverse
  Approx
  approximationWitness
  L =
  fractalLimitClosure
    Approx
    approximationWitness
    (limitSeparation-from-left-inverse L)

------------------------------------------------------------------------
-- E-graph/A* interpretation boundary.
--
-- The graph/search layer may discover this composition:
--
--   global-left-inverse
--     -> global-injectivity
--     -> finite/indexed fractal injectivity
--     -> compatible limit
--     -> surviving limit-left-inverse
--     -> limit separation
--     -> arbitrary-limit injectivity
--
-- The final equality is still an Agda proof term; A* cost/heuristic data
-- never becomes semantic evidence.
------------------------------------------------------------------------

record GRUFractalLimitCompositionKernel
  (State Observation LimitObservation : Set)
  (limitEncode : State → LimitObservation)
  : Set₁ where
  constructor gruFractalLimitCompositionKernel
  field
    limitInverse : LimitLeftInverse State LimitObservation limitEncode

open GRUFractalLimitCompositionKernel public

gruFractalLimitComposition-limitInjective :
  ∀ {State Observation LimitObservation : Set}
  {limitEncode : State → LimitObservation}
  (K :
    GRUFractalLimitCompositionKernel
      State Observation LimitObservation
      limitEncode) →
  ∀ {s t : State} →
  limitEncode s ＝ limitEncode t →
  s ＝ t
gruFractalLimitComposition-limitInjective K =
  limitInjective-from-left-inverse (limitInverse K)

------------------------------------------------------------------------
-- A typed e-graph path remains a semantic equality certificate.
------------------------------------------------------------------------

gruFractalLimitComposition-path-sound :
  ∀ {Expression State : Set}
  {R : EGraphSemanticInterpretation Expression State}
  {e f : Expression} →
  EGraphSemanticPath R e f →
  interpret R e ＝ interpret R f
gruFractalLimitComposition-path-sound =
  eGraph-path-sound _

------------------------------------------------------------------------
-- Canonical theorem section: GRU fractal limit convergence adapter.
------------------------------------------------------------------------

record GRUFractalLimitConvergenceWitness
  (Level State Observation LimitObservation : Set)
  (Refines : Level → Level → Set)
  (encode : Level → State → Observation)
  (limitEncode : State → LimitObservation)
  (rank : ℕ → Level)
  (Converges : (ℕ → Observation) → LimitObservation → Set)
  : Set₁ where
  constructor gruFractalLimitConvergenceWitness
  field
    approximationSequence :
      State → ℕ → Observation
    rankEncoding :
      ∀ n state →
      approximationSequence state n ＝
      encode (rank n) state
    converges :
      ∀ state →
      Converges
        (approximationSequence state)
        (limitEncode state)
    Approx :
      Observation → LimitObservation → Set
    approximationWitness :
      ∀ level state →
      Approx
        (encode level state)
        (limitEncode state)
    coherentDecoder :
      CoherentLimitDecoder
        Level State Observation LimitObservation
        encode limitEncode
    finiteLeftInverse :
      ∀ level state →
      CoherentLimitDecoder.decode
        coherentDecoder
        level
        (encode level state) ＝
      state

open GRUFractalLimitConvergenceWitness public

gruFractalLimitConvergence-limitLeftInverse :
  ∀ {Level State Observation LimitObservation : Set}
  {Refines : Level → Level → Set}
  {encode : Level → State → Observation}
  {limitEncode : State → LimitObservation}
  {rank : ℕ → Level}
  {Converges : (ℕ → Observation) → LimitObservation → Set}
  (W :
    GRUFractalLimitConvergenceWitness
      Level State Observation LimitObservation
      Refines encode limitEncode rank Converges) →
  LimitLeftInverse State LimitObservation limitEncode
gruFractalLimitConvergence-limitLeftInverse W =
  limitLeftInverse
    (λ state →
      coherentLimitDecoder-left-inverse
        (coherentDecoder W)
        (rank zero)
        state
        (finiteLeftInverse W (rank zero) state))

gruFractalLimitConvergence-fractalLimitClosure :
  ∀ {Level State Observation LimitObservation : Set}
  {Refines : Level → Level → Set}
  {encode : Level → State → Observation}
  {limitEncode : State → LimitObservation}
  {rank : ℕ → Level}
  {Converges : (ℕ → Observation) → LimitObservation → Set}
  (W :
    GRUFractalLimitConvergenceWitness
      Level State Observation LimitObservation
      Refines encode limitEncode rank Converges) →
  FractalLimitClosure
    Level State Observation LimitObservation
    Refines encode limitEncode
gruFractalLimitConvergence-fractalLimitClosure W =
  fractalLimitClosure
    (Approx W)
    (approximationWitness W)
    (limitSeparation-from-left-inverse
      (gruFractalLimitConvergence-limitLeftInverse W))

gruFractalLimitConvergence-limitInjective :
  ∀ {Level State Observation LimitObservation : Set}
  {Refines : Level → Level → Set}
  {encode : Level → State → Observation}
  {limitEncode : State → LimitObservation}
  {rank : ℕ → Level}
  {Converges : (ℕ → Observation) → LimitObservation → Set}
  (W :
    GRUFractalLimitConvergenceWitness
      Level State Observation LimitObservation
      Refines encode limitEncode rank Converges) →
  ∀ {s t : State} →
  limitEncode s ＝ limitEncode t →
  s ＝ t
gruFractalLimitConvergence-limitInjective W =
  fractalLimitInjective
    (gruFractalLimitConvergence-fractalLimitClosure W)

------------------------------------------------------------------------
-- Convergence remains a supplied witness. It is not promoted into a
-- separation theorem without the explicit coherent decoder/left inverse.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Canonical theorem section: GRU fractal limit convergence impossibility boundary.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Impossibility boundary for naive arbitrary-limit closure.
--
-- A convergence/approximation interface without a surviving separating
-- decoder cannot, by itself, imply injectivity of the limit representation.
-- The countermodel below is deliberately finite: Bool is collapsed to Unit.
------------------------------------------------------------------------


false-not-true : ¬ (false ＝ true)
false-not-true ()

constant-limit : Bool → ⊤
constant-limit _ = tt

trivial-convergence :
  ∀ state →
  ⊤
trivial-convergence _ = tt

------------------------------------------------------------------------
-- There cannot be a generic theorem that turns an arbitrary supplied
-- "convergence witness" into limit injectivity.  The premises below are
-- intentionally no stronger than a total witness for every state.
------------------------------------------------------------------------

naive-limit-injectivity-impossible :
  ¬
  (∀ {State LimitObservation : Set}
    (limitEncode : State → LimitObservation) →
    (∀ state → ⊤) →
    ∀ {s t : State} →
    limitEncode s ＝ limitEncode t →
    s ＝ t)
naive-limit-injectivity-impossible derive =
  false-not-true
    (derive constant-limit trivial-convergence
      {s = false} {t = true} refl)

------------------------------------------------------------------------
-- Interpretation:
--
--   approximation/convergence witness alone
--              ↛
--        limit injectivity
--
-- A separate separation mechanism is necessary.  The repository's
-- limit-left-inverse kernel supplies exactly that missing mechanism.
------------------------------------------------------------------------

record CanonicalAQLoopTheorem : Set₁ where
  constructor canonicalAQLoopTheorem
  field
    policyComposition :
      ∀ K s →
      C.canonicalPolicy K s ＝
      C.sparsemaxPolicy
        (C.actionSpaceK K)
        (C.lcbScore
          (C.lcbKernel K)
          (C.lcbCounts s)
          (C.critic (C.watkins s)))
        (C.valuesCount (C.lcbCounts s))
    sharedWatkinsSignal :
      ∀ K s →
      C.canonicalSignal K s ＝
      C.canonicalWatkinsTarget K s
    gruHaarInputCoupling :
      ∀ K s →
      C.canonicalGRUStep K s ＝
      C.gruStep (C.gru s) (C.canonicalHaarRecurrentInput K s)
    f4SignalCoupling :
      ∀ K s →
      C.canonicalOptimizerStep K s ＝
      C.f4ThetaStep (C.optimizerKernel K) (C.optimizer s) (C.canonicalSignal K s)
    watkinsEndogenousCoupling :
      ∀ K s →
      C.canonicalWatkinsTarget K s ＝
      C.intCodeAdd
        (C.intCodeAdd
          (C.intCodeAdd
            (C.canonicalReward8 K s)
            (C.canonicalQLogBias K s))
          (C.intCodeMul C.canonicalDiscount8
            (C.maxCriticValue8 (C.critic (C.watkins s)))))
        (C.canonicalEndogenousFeedback K s)

open CanonicalAQLoopTheorem public

canonical-aq-loop-theorem :
  CanonicalAQLoopTheorem
canonical-aq-loop-theorem =
  canonicalAQLoopTheorem
    (λ K s → refl)
    (λ K s → refl)
    C.canonicalRecurrentInput-law
    (λ K s → refl)
    (λ K s → refl)

canonicalAperiodic-theorem :
  ∀ K s n →
  C.iterateCanonical K (succ n) s ≢ s
canonicalAperiodic-theorem = C.canonicalAperiodic

canonicalNoNontrivialFiniteCycle-theorem :
  ∀ K s n →
  C.iterateCanonical K (succ n) s ＝ s → ⊥
canonicalNoNontrivialFiniteCycle-theorem = C.canonicalNoNontrivialFiniteCycle

record StateIsomorphism (A B : Set) : Set where
  constructor stateIsomorphism
  field
    to : A → B
    from : B → A
    from-to : ∀ a → from (to a) ＝ a
    to-from : ∀ b → to (from b) ＝ b

open StateIsomorphism public

iterateIsomorphism :
  ∀ {A : Set} → (A → A) → ℕ → A → A
iterateIsomorphism f zero a = a
iterateIsomorphism f (succ n) a = iterateIsomorphism f n (f a)

record StepConjugacyWitness
  (A B : Set)
  (sourceStep : A → A)
  (targetStep : B → B) : Set₁ where
  constructor stepConjugacyWitness
  field
    isomorphism : StateIsomorphism A B
    stepCommutes :
      ∀ a →
      to isomorphism (sourceStep a) ＝
      targetStep (to isomorphism a)

open StepConjugacyWitness public

stepConjugacy-iterate :
  ∀ {A B : Set}
  {sourceStep : A → A}
  {targetStep : B → B}
  (W : StepConjugacyWitness A B sourceStep targetStep)
  (n : ℕ)
  (a : A) →
  to (isomorphism W) (iterateIsomorphism sourceStep n a) ＝
  iterateIsomorphism targetStep n (to (isomorphism W) a)
stepConjugacy-iterate {sourceStep = sourceStep} {targetStep = targetStep} W zero a =
  refl
stepConjugacy-iterate {sourceStep = sourceStep} {targetStep = targetStep} W (succ n) a =
  trans
    (stepConjugacy-iterate {sourceStep = sourceStep} {targetStep = targetStep} W n (sourceStep a))
    (ap
      (iterateIsomorphism targetStep n)
      (stepCommutes W a))

iteratePredicateTransport :
  ∀ {B : Set}
  (step : B → B)
  (Property : B → Set) →
  (∀ b → Property b → Property (step b)) →
  ∀ n b →
  Property b →
  Property (iterateIsomorphism step n b)
iteratePredicateTransport step Property preserved zero b proof =
  proof
iteratePredicateTransport step Property preserved (succ n) b proof =
  iteratePredicateTransport
    step
    Property
    preserved
    n
    (step b)
    (preserved b proof)

stepConjugacy-property-transport :
  ∀ {A B : Set}
  {sourceStep : A → A}
  {targetStep : B → B}
  (W : StepConjugacyWitness A B sourceStep targetStep)
  (P : A → Set)
  (Q : B → Set)
  (bridge : ∀ a → P a → Q (to (isomorphism W) a))
  (preserved : ∀ b → Q b → Q (targetStep b)) →
  ∀ n a →
  P a →
  Q (iterateIsomorphism targetStep n (to (isomorphism W) a))
stepConjugacy-property-transport {targetStep = targetStep} W P Q bridge preserved n a proof =
  iteratePredicateTransport
    targetStep
    Q
    preserved
    n
    (to (isomorphism W) a)
    (bridge a proof)

data LearnerReplacement : Set where
  optimizerReplacement : F4IntUState → LearnerReplacement

applyLearnerReplacement :
  LearnerReplacement → FullLearnerState → FullLearnerState
applyLearnerReplacement (optimizerReplacement o) s = replaceOptimizer s o

applyLearnerReplacements :
  List LearnerReplacement → FullLearnerState → FullLearnerState
applyLearnerReplacements [] s = s
applyLearnerReplacements (r ∷ rs) s =
  applyLearnerReplacements rs (applyLearnerReplacement r s)

canonicalPolicy-learnerReplacement-invariant :
  ∀ K s r →
  canonicalPolicy K (applyLearnerReplacement r s) ＝ canonicalPolicy K s
canonicalPolicy-learnerReplacement-invariant K s (optimizerReplacement o) =
  canonicalPolicy-optimizer-invariant K s o

canonicalPolicy-learnerReplacement-composition :
  ∀ K s rs →
  canonicalPolicy K (applyLearnerReplacements rs s) ＝ canonicalPolicy K s
canonicalPolicy-learnerReplacement-composition K s [] = refl
canonicalPolicy-learnerReplacement-composition K s (r ∷ rs) =
  trans
    (canonicalPolicy-learnerReplacement-composition
      K (applyLearnerReplacement r s) rs)
    (canonicalPolicy-learnerReplacement-invariant K s r)

canonicalPersistentGRU-afterFullStep-iterate :
  ∀ K n s →
  persistentGRU
    (gru (iterateCanonical K n s))
  ＝
  persistentGRU (gru s)
canonicalPersistentGRU-afterFullStep-iterate K zero s = refl
canonicalPersistentGRU-afterFullStep-iterate K (succ n) s =
  trans
    (canonicalPersistentGRU-afterFullStep-iterate
      K n (canonicalFullStep K s))
    (canonicalPersistentGRUPreservation K s)

record EqualityCompositionTheorem
  {A : Set}
  {x y z : A} : Set where
  constructor equalityCompositionTheorem
  field
    firstStep : x ＝ y
    secondStep : y ＝ z
    composedStep : x ＝ z

composeEqualityTheorem :
  ∀ {A : Set} {x y z : A} →
  x ＝ y →
  y ＝ z →
  EqualityCompositionTheorem
composeEqualityTheorem first second =
  equalityCompositionTheorem
    first
    second
    (trans first second)

record RecurrentAssociativeScanTheorem
  (State Input : Set) : Set₁ where
  constructor recurrentAssociativeScanTheorem
  field
    actionAssociative :
      ∀ (f g h : C.Endomorphism State) s →
      C.applyEndomorphism
        (C.composeEndomorphism
          (C.composeEndomorphism f g)
          h)
        s
      ＝
      C.applyEndomorphism
        (C.composeEndomorphism
          f
          (C.composeEndomorphism g h))
        s

    prefixCorrect :
      ∀ (R : C.RecurrentNetwork State Input)
        (xs : ℕ → Input)
        (n : ℕ)
        (s : State) →
      C.applyEndomorphism
        (C.recurrentPrefixEndomorphism R xs n)
        s
      ＝
      C.recurrentPrefixState R xs n s

    prefixSplit :
      ∀ (R : C.RecurrentNetwork State Input)
        (xs : ℕ → Input)
        (m n : ℕ)
        (s : State) →
      C.recurrentPrefixState R xs (m + n) s
      ＝
      C.recurrentPrefixState
        R
        (C.shiftInput xs m)
        n
        (C.recurrentPrefixState R xs m s)

canonicalGRU-recurrent-associative-scan-theorem :
  RecurrentAssociativeScanTheorem C.GRUState C.IntCode
canonicalGRU-recurrent-associative-scan-theorem =
  recurrentAssociativeScanTheorem
    C.endomorphismAssociative
    C.recurrentPrefix-correct
    C.recurrentPrefix-split

prefixOp :
  ∀ {State : Set} →
  C.Endomorphism State →
  C.Endomorphism State →
  C.Endomorphism State
prefixOp f g = C.composeEndomorphism g f

prefixListEndomorphism :
  ∀ {State Input : Set} →
  C.RecurrentNetwork State Input →
  List Input →
  C.Endomorphism State
prefixListEndomorphism R [] =
  C.identityEndomorphism
prefixListEndomorphism R (x ∷ xs) =
  C.composeEndomorphism
    (prefixListEndomorphism R xs)
    (C.recurrentInputEndomorphism R x)

prefixListEndomorphism-unit :
  ∀ {State Input : Set}
  (R : C.RecurrentNetwork State Input)
  (s : State) →
  C.applyEndomorphism
    (prefixListEndomorphism R [])
    s
  ＝ s
prefixListEndomorphism-unit R s = refl

prefixListEndomorphism-append :
  ∀ {State Input : Set}
  (R : C.RecurrentNetwork State Input)
  (xs ys : List Input)
  (s : State) →
  C.applyEndomorphism
    (prefixListEndomorphism R (xs ++ ys))
    s
  ＝
  C.applyEndomorphism
    (prefixOp
      (prefixListEndomorphism R xs)
      (prefixListEndomorphism R ys))
    s
prefixListEndomorphism-append R [] ys s = refl
prefixListEndomorphism-append R (x ∷ xs) ys s =
  trans
    (prefixListEndomorphism-append
      R
      xs
      ys
      (C.applyEndomorphism
        (C.recurrentInputEndomorphism R x)
        s))
    refl

prefixOp-associative :
  ∀ {State : Set}
  (f g h : C.Endomorphism State)
  (s : State) →
  C.applyEndomorphism
    (prefixOp (prefixOp f g) h)
    s
  ＝
  C.applyEndomorphism
    (prefixOp f (prefixOp g h))
    s
prefixOp-associative f g h s =
  C.endomorphismAssociative h g f s

prefixOp-identity-left :
  ∀ {State : Set}
  (f : C.Endomorphism State) (s : State) →
  C.applyEndomorphism (prefixOp C.identityEndomorphism f) s
  ＝ C.applyEndomorphism f s
prefixOp-identity-left f s = refl

prefixOp-identity-right :
  ∀ {State : Set}
  (f : C.Endomorphism State) (s : State) →
  C.applyEndomorphism (prefixOp f C.identityEndomorphism) s
  ＝ C.applyEndomorphism f s
prefixOp-identity-right f s = refl

record RecurrentPrefixMonoidHomomorphism
  (State Input : Set) : Set₁ where
  constructor recurrentPrefixMonoidHomomorphism
  field
    unit :
      ∀ (R : C.RecurrentNetwork State Input) (s : State) →
      C.applyEndomorphism
        (prefixListEndomorphism R [])
        s
      ＝ s
    append :
      ∀ (R : C.RecurrentNetwork State Input)
        (xs ys : List Input)
        (s : State) →
      C.applyEndomorphism
        (prefixListEndomorphism R (xs ++ ys))
        s
      ＝
      C.applyEndomorphism
        (prefixOp
          (prefixListEndomorphism R xs)
          (prefixListEndomorphism R ys))
        s

canonical-recurrent-prefix-monoid-homomorphism :
  RecurrentPrefixMonoidHomomorphism C.GRUState C.IntCode
canonical-recurrent-prefix-monoid-homomorphism =
  recurrentPrefixMonoidHomomorphism
    (λ R s → prefixListEndomorphism-unit R s)
    (λ R xs ys s → prefixListEndomorphism-append R xs ys s)

productEndomorphism :
  ∀ {StateA StateB : Set} →
  C.Endomorphism StateA →
  C.Endomorphism StateB →
  C.Endomorphism (StateA × StateB)
productEndomorphism f g =
  C.endomorphism
    (λ st →
      (C.applyEndomorphism f (pr₁ st) ,
       C.applyEndomorphism g (pr₂ st)))

productEndomorphism-compose :
  ∀ {StateA StateB : Set}
  (f₁ f₂ : C.Endomorphism StateA)
  (g₁ g₂ : C.Endomorphism StateB)
  (s : StateA)
  (t : StateB) →
  C.applyEndomorphism
    (productEndomorphism
      (C.composeEndomorphism f₁ f₂)
      (C.composeEndomorphism g₁ g₂))
    (s , t)
  ＝
  C.applyEndomorphism
    (C.composeEndomorphism
      (productEndomorphism f₁ g₁)
      (productEndomorphism f₂ g₂))
    (s , t)
productEndomorphism-compose f₁ f₂ g₁ g₂ s t = refl

canonicalF4RecurrentNetwork :
  C.CanonicalFullLearnerKernel →
  C.RecurrentNetwork C.F4IntUState C.IntCode
canonicalF4RecurrentNetwork K =
  C.recurrentNetwork
    (λ o signal →
      C.f4ThetaStep (C.optimizerKernel K) o signal)

canonicalF4RecurrentNetwork-step-law :
  ∀ (K : C.CanonicalFullLearnerKernel)
  (o : C.F4IntUState)
  (signal : C.IntCode) →
  C.runNetwork
    (canonicalF4RecurrentNetwork K)
    o
    signal
  ＝
  C.f4ThetaStep (C.optimizerKernel K) o signal
canonicalF4RecurrentNetwork-step-law K o signal = refl

canonicalF4-prefix-monoid-homomorphism :
  RecurrentPrefixMonoidHomomorphism
    C.F4IntUState
    C.IntCode
canonicalF4-prefix-monoid-homomorphism =
  recurrentPrefixMonoidHomomorphism
    (λ R s → prefixListEndomorphism-unit R s)
    (λ R xs ys s → prefixListEndomorphism-append R xs ys s)

CanonicalGRUF4PrefixState : Set
CanonicalGRUF4PrefixState =
  C.GRUState × C.F4IntUState

CanonicalGRUF4PrefixInput : Set
CanonicalGRUF4PrefixInput =
  C.IntCode × C.IntCode

canonicalGRUF4PrefixNetwork :
  C.CanonicalFullLearnerKernel →
  C.RecurrentNetwork
    CanonicalGRUF4PrefixState
    CanonicalGRUF4PrefixInput
canonicalGRUF4PrefixNetwork K =
  C.recurrentNetwork
    (λ { (g , o) (gruInput , optimizerInput) →
      ( C.gruStep g gruInput
      , C.f4ThetaStep (C.optimizerKernel K) o optimizerInput ) })

canonicalGRUF4Prefix-step-law :
  ∀ (K : C.CanonicalFullLearnerKernel)
  (g : C.GRUState) (o : C.F4IntUState)
  (gruInput optimizerInput : C.IntCode) →
  C.runNetwork (canonicalGRUF4PrefixNetwork K)
    (g , o) (gruInput , optimizerInput)
  ＝
  ( C.gruStep g gruInput
  , C.f4ThetaStep (C.optimizerKernel K) o optimizerInput )
canonicalGRUF4Prefix-step-law K g o gruInput optimizerInput = refl

canonicalGRUF4-prefix-monoid-homomorphism :
  RecurrentPrefixMonoidHomomorphism
    CanonicalGRUF4PrefixState
    CanonicalGRUF4PrefixInput
canonicalGRUF4-prefix-monoid-homomorphism =
  recurrentPrefixMonoidHomomorphism
    (λ R s → prefixListEndomorphism-unit R s)
    (λ R xs ys s → prefixListEndomorphism-append R xs ys s)

canonicalFullStep-GRUF4-prefix-bridge :
  ∀ (K : C.CanonicalFullLearnerKernel)
  (s : C.CanonicalFullLearnerState) →
  C.runNetwork (canonicalGRUF4PrefixNetwork K)
    (C.gru s , C.optimizer s)
    (C.canonicalHaarRecurrentInput K s , C.canonicalSignal K s)
  ＝
  ( C.gru (C.canonicalFullStep K s)
  , C.optimizer (C.canonicalFullStep K s))
canonicalFullStep-GRUF4-prefix-bridge K s = refl

record CanonicalGRUF4WatkinsPrefixCompositionTheorem : Set₁ where
  constructor canonicalGRUF4WatkinsPrefixCompositionTheorem
  field
    recurrentScan :
      RecurrentPrefixMonoidHomomorphism C.GRUState C.IntCode
    targetCorrectness :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (s : C.CanonicalFullLearnerState) →
      C.canonicalSignal K s ＝ C.canonicalWatkinsTarget K s
    gruf4Correctness :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (s : C.CanonicalFullLearnerState) →
      C.runNetwork (canonicalGRUF4PrefixNetwork K)
        (C.gru s , C.optimizer s)
        (C.canonicalHaarRecurrentInput K s , C.canonicalSignal K s)
      ＝
      ( C.gru (C.canonicalFullStep K s)
      , C.optimizer (C.canonicalFullStep K s))

canonical-gruf4-watkins-prefix-composition-theorem :
  CanonicalGRUF4WatkinsPrefixCompositionTheorem
canonical-gruf4-watkins-prefix-composition-theorem =
  canonicalGRUF4WatkinsPrefixCompositionTheorem
    canonical-recurrent-prefix-monoid-homomorphism
    C.canonicalSignal-watkins-target
    canonicalFullStep-GRUF4-prefix-bridge

commutingIterate :
  ∀ {S : Set} →
  (S → S) → ℕ → S → S
commutingIterate step zero s = s
commutingIterate step (succ n) s =
  step (commutingIterate step n s)

record CommutingSquareTheorem
  (State Feature : Set)
  (step : State → State)
  (observe : State → Feature)
  (featureStep : Feature → Feature) : Set₁ where
  constructor commutingSquareTheorem
  field
    square :
      ∀ s → observe (step s) ＝ featureStep (observe s)
    iterateSquare :
      ∀ n s →
      observe (commutingIterate step n s) ＝
      commutingIterate featureStep n (observe s)

open CommutingSquareTheorem public

commutingSquareTheorem-from-square :
  ∀ {State Feature : Set}
  {step : State → State}
  {observe : State → Feature}
  {featureStep : Feature → Feature} →
  (∀ s → observe (step s) ＝ featureStep (observe s)) →
  CommutingSquareTheorem State Feature step observe featureStep
commutingSquareTheorem-from-square {step = step} {observe = observe} {featureStep = featureStep} square =
  commutingSquareTheorem
    square
    deriveIterateSquare
  where
    deriveIterateSquare :
      ∀ n s →
      observe (commutingIterate step n s) ＝
      commutingIterate featureStep n (observe s)
    deriveIterateSquare zero s = refl
    deriveIterateSquare (succ n) s =
      trans
        (square (commutingIterate step n s))
        (ap featureStep (deriveIterateSquare n s))

record FreeMonoidActionHomomorphism
  (State Feature : Set)
  (step : State → State)
  (observe : State → Feature)
  (featureStep : Feature → Feature) : Set₁ where
  constructor freeMonoidActionHomomorphism
  field
    iterateHomomorphism :
      ∀ n s →
      observe (commutingIterate step n s) ＝
      commutingIterate featureStep n (observe s)

open FreeMonoidActionHomomorphism public

freeMonoidActionHomomorphism-from-square :
  ∀ {State Feature : Set}
  {step : State → State}
  {observe : State → Feature}
  {featureStep : Feature → Feature} →
  CommutingSquareTheorem State Feature step observe featureStep →
  FreeMonoidActionHomomorphism State Feature step observe featureStep
freeMonoidActionHomomorphism-from-square squareWitness =
  freeMonoidActionHomomorphism
    (CommutingSquareTheorem.iterateSquare squareWitness)

canonicalCount-freeMonoidActionHomomorphism :
  ∀ (K : C.CanonicalFullLearnerKernel) →
  FreeMonoidActionHomomorphism
    C.CanonicalFullLearnerState
    ℕ
    (C.canonicalFullStep K)
    succ
    (λ s → C.totalCount (C.lcbCounts s))
canonicalCount-freeMonoidActionHomomorphism K =
  freeMonoidActionHomomorphism-from-square
    (commutingSquareTheorem-from-square
      (λ s →
        C.canonicalTotalCountStep K s))

recurrentWordState :
  ∀ {State Input : Set} →
  C.RecurrentNetwork State Input →
  List Input →
  State →
  State
recurrentWordState R word s =
  C.applyEndomorphism
    (prefixListEndomorphism R word)
    s

recurrentPrefix-scan-lifts-conjugacy :
  ∀ {State Input : Set}
  (replace : State → State)
  (step : State → Input → State)
  (h :
    ∀ (s : State) (x : Input) →
    replace (step s x) ＝ step (replace s) x) →
  ∀ (xs : List Input) (n : ℕ) (s : State) →
    replace
      (C.recurrentPrefixState
        (C.recurrentNetwork step)
        xs n s)
    ＝
    C.recurrentPrefixState
      (C.recurrentNetwork step)
      xs n
      (replace s)
recurrentPrefix-scan-lifts-conjugacy replace step h xs zero s = refl
recurrentPrefix-scan-lifts-conjugacy replace step h xs (succ n) s =
  trans
    (recurrentPrefix-scan-lifts-conjugacy
      replace
      step
      h
      xs
      n
      (step s (xs n)))
    (ap
      (λ q →
        C.recurrentPrefixState
          (C.recurrentNetwork step)
          xs n
          q)
      (h s (xs n)))

record RecurrentScanConjugacyTheorem
  (State Input : Set) : Set₁ where
  constructor recurrentScanConjugacyTheorem
  field
    replacement :
      ∀ (replace : State → State)
        (step : State → Input → State) →
        (h :
          ∀ (s : State) (x : Input) →
          replace (step s x) ＝ step (replace s) x) →
        State → State
    scanConjugacy :
      ∀ (replace : State → State)
        (step : State → Input → State) →
        (h :
          ∀ (s : State) (x : Input) →
          replace (step s x) ＝ step (replace s) x) →
        (xs : List Input) →
        (n : ℕ) →
        (s : State) →
        replace
          (C.recurrentPrefixState
            (C.recurrentNetwork step)
            xs n s) ＝
        C.recurrentPrefixState
          (C.recurrentNetwork step)
          xs n
          (replace s)

open RecurrentScanConjugacyTheorem public

canonical-recurrent-scan-conjugacy-theorem :
  RecurrentScanConjugacyTheorem C.GRUState C.IntCode
canonical-recurrent-scan-conjugacy-theorem =
  recurrentScanConjugacyTheorem
    (λ replace step h → replace)
    (λ replace step h xs n s →
      recurrentPrefix-scan-lifts-conjugacy replace step h xs n s)


record CanonicalFullLearnerConnectedScanConjugacyTheorem : Set₁ where
  constructor canonicalFullLearnerConnectedScanConjugacyTheorem
  field
    scanConjugacy :
      (replace : C.CanonicalFullLearnerState → C.CanonicalFullLearnerState)
      (K : C.CanonicalFullLearnerKernel) →
      (h :
        ∀ s →
        replace (C.canonicalFullStep K s) ＝
        C.canonicalFullStep K (replace s)) →
      ∀ n s →
        replace (C.iterateCanonical K n s) ＝
        C.iterateCanonical K n (replace s)
    connectedStep :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (s : C.CanonicalFullLearnerState) →
      C.runNetwork (canonicalGRUF4PrefixNetwork K)
        (C.gru s , C.optimizer s)
        (C.canonicalHaarRecurrentInput K s , C.canonicalSignal K s)
      ＝
      ( C.gru (C.canonicalFullStep K s)
      , C.optimizer (C.canonicalFullStep K s))
    watkinsConnected :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (s : C.CanonicalFullLearnerState) →
      C.watkins (C.canonicalFullStep K s) ＝
      C.canonicalWatkinsStep K s
    watkinsTargetCoupling :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (s : C.CanonicalFullLearnerState) →
      C.canonicalSignal K s ＝ C.canonicalWatkinsTarget K s
    gruHaarInputCoupling :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (s : C.CanonicalFullLearnerState) →
      C.canonicalGRUStep K s ＝
      C.gruStep
        (C.gru s)
        (C.canonicalHaarRecurrentInput K s)
    optimizerWatkinsCoupling :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (s : C.CanonicalFullLearnerState) →
      C.canonicalOptimizerStep K s ＝
      C.f4ThetaStep
        (C.optimizerKernel K)
        (C.optimizer s)
        (C.canonicalWatkinsTarget K s)

canonicalFullLearner-iterate-conjugacy :
  ∀
  (replace : C.CanonicalFullLearnerState → C.CanonicalFullLearnerState)
  (K : C.CanonicalFullLearnerKernel)
  (h :
    ∀ s →
    replace (C.canonicalFullStep K s) ＝
    C.canonicalFullStep K (replace s)) →
  ∀ n s →
  replace (C.iterateCanonical K n s) ＝
  C.iterateCanonical K n (replace s)
canonicalFullLearner-iterate-conjugacy replace K h zero s = refl
canonicalFullLearner-iterate-conjugacy replace K h (succ n) s =
  trans
    (canonicalFullLearner-iterate-conjugacy
      replace K h n (C.canonicalFullStep K s))
    (ap
      (C.iterateCanonical K n)
      (h s))

canonical-full-learner-connected-scan-conjugacy-theorem :
  CanonicalFullLearnerConnectedScanConjugacyTheorem
canonical-full-learner-connected-scan-conjugacy-theorem =
  canonicalFullLearnerConnectedScanConjugacyTheorem
    (λ replace K h → canonicalFullLearner-iterate-conjugacy replace K h)
    canonicalFullStep-GRUF4-prefix-bridge
    C.canonicalFullStep-watkins
    C.canonicalSignal-watkins-target
    C.canonicalRecurrentInput-law
    C.canonicalOptimizerStep-qMunchausen-L2
record S4PlusS5RecurrentScanTheorem (State Input : Set) : Set₁ where
  constructor s4PlusS5RecurrentScanTheorem
  field
    recurrentScan :
      RecurrentAssociativeScanTheorem State Input
    identityAction :
      ∀ (s : State) →
      C.applyEndomorphism
        C.identityEndomorphism s ＝ s

open S4PlusS5RecurrentScanTheorem public

canonical-S4S5-recurrent-scan-theorem :
  S4PlusS5RecurrentScanTheorem C.GRUState C.IntCode
canonical-S4S5-recurrent-scan-theorem =
  s4PlusS5RecurrentScanTheorem
    canonicalGRU-recurrent-associative-scan-theorem
    (λ s → refl)

productRecurrentNetwork :
  ∀ {StateA StateB Input : Set} →
  C.RecurrentNetwork StateA Input →
  C.RecurrentNetwork StateB Input →
  C.RecurrentNetwork (StateA × StateB) Input
productRecurrentNetwork RA RB =
  C.recurrentNetwork
    (λ st x →
      (C.runNetwork RA (pr₁ st) x ,
       C.runNetwork RB (pr₂ st) x))

productRecurrentPrefix-correct :
  ∀ {StateA StateB Input : Set}
  (RA : C.RecurrentNetwork StateA Input)
  (RB : C.RecurrentNetwork StateB Input)
  (xs : ℕ → Input)
  (n : ℕ)
  (s : StateA)
  (t : StateB) →
  C.recurrentPrefixState
    (productRecurrentNetwork RA RB)
    xs n
    (s , t)
  ＝
  (C.recurrentPrefixState RA xs n s ,
   C.recurrentPrefixState RB xs n t)
productRecurrentPrefix-correct RA RB xs zero s t = refl
productRecurrentPrefix-correct RA RB xs (succ n) s t =
  cong₂
    (λ a b →
      (C.runNetwork RA a (xs n) ,
       C.runNetwork RB b (xs n)))
    (ap pr₁ (productRecurrentPrefix-correct RA RB xs n s t))
    (ap pr₂ (productRecurrentPrefix-correct RA RB xs n s t))

informationPreserving-symbolic-task-factorization :
  ∀ {State Feature Output : Set}
  (observe : State → Feature)
  (inverse : Feature → State)
  (leftInverse : ∀ s → inverse (observe s) ＝ s)
  (target : State → Output)
  (s : State) →
  target s ＝ target (inverse (observe s))
informationPreserving-symbolic-task-factorization
  observe inverse leftInverse target s =
  ap target (sym (leftInverse s))

informationPreserving-all-tasks-injective :
  ∀ {State Feature : Set}
  (observe : State → Feature)
  (inverse : Feature → State) →
  (∀ (target : State → State) (s : State) →
    target s ＝ target (inverse (observe s))) →
  ∀ {s t} → observe s ＝ observe t → s ＝ t
informationPreserving-all-tasks-injective
  observe inverse allTasks
  {s} {t} eq =
  trans
    (sym (allTasks (λ x → x) s))
    (trans
      apply-cong eq
      (allTasks (λ x → x) t))

productObservation :
  ∀ {StateA StateB FeatureA FeatureB : Set} →
  (StateA → FeatureA) →
  (StateB → FeatureB) →
  (StateA × StateB) →
  (FeatureA × FeatureB)
productObservation observeA observeB st =
  (observeA (pr₁ st) , observeB (pr₂ st))

productInverse :
  ∀ {StateA StateB FeatureA FeatureB : Set} →
  (FeatureA → StateA) →
  (FeatureB → StateB) →
  (FeatureA × FeatureB) →
  (StateA × StateB)
productInverse inverseA inverseB feature =
  (inverseA (pr₁ feature) , inverseB (pr₂ feature))

productObservation-leftInverse :
  ∀ {StateA StateB FeatureA FeatureB : Set}
  (observeA : StateA → FeatureA)
  (inverseA : FeatureA → StateA)
  (observeB : StateB → FeatureB)
  (inverseB : FeatureB → StateB)
  (leftInverseA : ∀ s → inverseA (observeA s) ＝ s)
  (leftInverseB : ∀ s → inverseB (observeB s) ＝ s)
  (s : StateA)
  (t : StateB) →
  productInverse inverseA inverseB
    (productObservation observeA observeB (s , t))
  ＝
  (s , t)
productObservation-leftInverse observeA inverseA observeB inverseB
  leftInverseA leftInverseB s t =
  cong₂ _,_ (leftInverseA s) (leftInverseB t)

informationPreserving-symbolic-task-boundary :
  ∀ {State Feature : Set}
  (observe : State → Feature)
  (inverse : Feature → State)
  (leftInverse : ∀ s → inverse (observe s) ＝ s) →
  ∀ (target : State → State) (s : State) →
  target s ＝ target (inverse (observe s))
informationPreserving-symbolic-task-boundary =
  informationPreserving-symbolic-task-factorization

record PointwiseSandwich
  {Input Value : Set}
  (_≤_ : Value → Value → Set)
  (lower actual upper : Input → Value) : Set₁ where
  constructor pointwiseSandwich
  field
    lower≤actual : ∀ x → lower x ≤ actual x
    actual≤upper : ∀ x → actual x ≤ upper x

record MinimaxBellmanShapleyOperator
  (State Value : Set)
  (_≤_ : Value → Value → Set) : Set₁ where
  constructor minimaxBellmanShapleyOperator
  field
    value : (State → Value) → Value
    monotone :
      ∀ (f g : State → Value) →
      (∀ s → f s ≤ g s) →
      value f ≤ value g

record MinimaxBellmanShapleyInclusionTheorem
  (State Value : Set)
  (_≤_ : Value → Value → Set)
  (operator : MinimaxBellmanShapleyOperator State Value _≤_)
  (lower actual upper : State → Value) : Set₁ where
  constructor minimaxBellmanShapleyInclusionTheorem
  field
    lowerBound :
      MinimaxBellmanShapleyOperator.value operator lower
      ≤
      MinimaxBellmanShapleyOperator.value operator actual
    upperBound :
      MinimaxBellmanShapleyOperator.value operator actual
      ≤
      MinimaxBellmanShapleyOperator.value operator upper

open PointwiseSandwich public
open MinimaxBellmanShapleyOperator public
open MinimaxBellmanShapleyInclusionTheorem public

canonicalBiasedWatkinsNegativeQMunchausenL2Target :
  C.CanonicalFullLearnerKernel → C.CanonicalFullLearnerState → C.IntCode
canonicalBiasedWatkinsNegativeQMunchausenL2Target =
  C.canonicalWatkinsTarget

canonical-qLog2Bias8-law :
  ∀ x →
  C.qLog2Bias8 x ＝
  C.intCodeNeg
    (C.intCodeOfNat
      (C.dyadicDivide
        (C.munchausenScale8 * C.dyadicNumerator (C.qLog8 x))
        (C.dyadicDenominator (C.qLog8 x))))
canonical-qLog2Bias8-law x with C.intCodeMagnitude x
... | zero = refl
... | succ n = refl


record CanonicalBiasedWatkinsNegativeQMunchausenL2TargetTheorem : Set₁ where
  constructor canonicalBiasedWatkinsNegativeQMunchausenL2TargetTheorem
  field
    negativeQMunchausenBias :
      ∀ x →
      C.qLog2Bias8 x ＝
      C.intCodeNeg
        (C.intCodeOfNat
          (C.dyadicDivide
            (C.munchausenScale8 * C.dyadicNumerator (C.qLog8 x))
            (C.dyadicDenominator (C.qLog8 x))))

    targetDecomposition :
      ∀ K s →
      canonicalBiasedWatkinsNegativeQMunchausenL2Target K s ＝
      C.intCodeAdd
        (C.intCodeAdd
          (C.intCodeAdd
            (C.canonicalReward8 K s)
            (C.canonicalQLogBias K s))
          (C.intCodeMul
            C.canonicalDiscount8
            (C.maxCriticValue8 (C.critic (C.watkins s)))))
        (C.canonicalEndogenousFeedback K s)

    l2ConsumesTarget :
      ∀ K s →
      C.canonicalOptimizerStep K s ＝
      C.f4ThetaStep
        (C.optimizerKernel K)
        (C.optimizer s)
        (canonicalBiasedWatkinsNegativeQMunchausenL2Target K s)

open CanonicalBiasedWatkinsNegativeQMunchausenL2TargetTheorem public

canonical-biased-watkins-negative-q-munchausen-l2-target-theorem :
  CanonicalBiasedWatkinsNegativeQMunchausenL2TargetTheorem
canonical-biased-watkins-negative-q-munchausen-l2-target-theorem =
  canonicalBiasedWatkinsNegativeQMunchausenL2TargetTheorem
    canonical-qLog2Bias8-law
    (λ K s → C.canonicalWatkinsTarget-law K s)
    (λ K s → C.canonicalOptimizerStep-qMunchausen-L2 K s)


record CanonicalQMunchausenL2SharedNegationPolarityTheorem : Set₁ where
  constructor canonicalQMunchausenL2SharedNegationPolarityTheorem
  field
    qMunchausenBiasNegation :
      ∀ x →
      C.qLog2Bias8 x ＝
      C.intCodeNeg
        (C.intCodeOfNat
          (C.dyadicDivide
            (C.munchausenScale8 * C.dyadicNumerator (C.qLog8 x))
            (C.dyadicDenominator (C.qLog8 x))))

    l2CorrectionNegation :
      ∀ x →
      C.l2Correction x ＝ C.intCodeNeg x

open CanonicalQMunchausenL2SharedNegationPolarityTheorem public

canonicalWatkinsTarget-endogenous-leftInverse :
  ∀ (K : C.CanonicalFullLearnerKernel)
  (observe : C.CanonicalFullLearnerState → C.IntCode)
  (inverse : C.IntCode → C.CanonicalFullLearnerState) →
  (leftInverse : ∀ t → inverse (observe t) ＝ t) →
  ∀ s →
  C.canonicalWatkinsTarget K s ＝
    C.intCodeAdd
      (C.intCodeAdd
        (C.intCodeAdd
          (C.canonicalReward8 K (inverse (observe s)))
          (C.canonicalQLogBias K (inverse (observe s))))
        (C.intCodeMul
          C.canonicalDiscount8
          (C.maxCriticValue8
            (C.critic
              (C.watkins
                (inverse (observe s)))))))
      (C.canonicalEndogenousFeedback K (inverse (observe s)))
canonicalWatkinsTarget-endogenous-leftInverse K observe inverse leftInverse s =
  trans
    (C.canonicalWatkinsTarget-law K s)
    (ap
      (λ t →
        C.intCodeAdd
          (C.intCodeAdd
            (C.intCodeAdd
              (C.canonicalReward8 K t)
              (C.canonicalQLogBias K t))
            (C.intCodeMul
              C.canonicalDiscount8
              (C.maxCriticValue8
                (C.critic (C.watkins t)))))
          (C.canonicalEndogenousFeedback K t))
      (leftInverse s))

succ-injective :
  ∀ {m n : ℕ} → succ m ＝ succ n → m ＝ n
succ-injective refl = refl

natPlus-left-cancel :
  ∀ (k m n : ℕ) → k + m ＝ k + n → m ＝ n
natPlus-left-cancel zero m n eq = eq
natPlus-left-cancel (succ k) m n eq =
  natPlus-left-cancel k m n (succ-injective eq)

canonicalOrbit-state-injective :
  ∀ K s {m n : ℕ} →
  C.iterateCanonical K m s ＝ C.iterateCanonical K n s →
  m ＝ n
canonicalOrbit-state-injective K s {m} {n} eq =
  natPlus-left-cancel
    (C.totalCount (C.lcbCounts s))
    m
    n
    (trans
      (sym (C.canonicalTotalCountAfter K m s))
      (trans
        (ap (λ t → C.totalCount (C.lcbCounts t)) eq)
        (C.canonicalTotalCountAfter K n s)))


record DiscreteExactUAPTheorem
  (State Feature Output : Set)
  (observe : State → Feature)
  (inverse : Feature → State) : Set₁ where
  constructor discreteExactUAPTheorem
  field
    leftInverse :
      ∀ s → inverse (observe s) ＝ s
    exactReadout :
      (target : State → Output) →
      ∀ s →
      target s ＝ target (inverse (observe s))

open DiscreteExactUAPTheorem public

record DiscreteLeftInverseWitness
  (State Feature : Set)
  (observe : State → Feature) : Set₁ where
  constructor discreteLeftInverseWitness
  field
    inverse : Feature → State
    leftInverse :
      ∀ s → inverse (observe s) ＝ s

open DiscreteLeftInverseWitness public

record DiscreteExactUniversalUAP
  (State Feature : Set)
  (observe : State → Feature) : Set₁ where
  constructor discreteExactUniversalUAP
  field
    readout :
      {Output : Set} →
      (State → Output) →
      Feature →
      Output
    exactReadout :
      {Output : Set} →
      (target : State → Output) →
      ∀ s →
      target s ＝ readout target (observe s)

open DiscreteExactUniversalUAP public

discreteLeftInverse-observe-injective :
  ∀ {State Feature : Set}
  {observe : State → Feature}
  {inverse : Feature → State} →
  (∀ s → inverse (observe s) ＝ s) →
  ∀ {s t} →
  observe s ＝ observe t →
  s ＝ t
discreteLeftInverse-observe-injective leftInverse {s} {t} eq =
  trans
    (sym (leftInverse s))
    (trans
      apply-cong eq
      (leftInverse t))

collision-implies-no-leftInverse-via-injectivity :
  ∀ {State Feature : Set}
  (observe : State → Feature)
  {s t : State} →
  observe s ＝ observe t →
  s ≢ t →
  ¬ (Σ (λ inverse →
      ∀ u → inverse (observe u) ＝ u))
collision-implies-no-leftInverse-via-injectivity
  observe obsEq distinct =
  λ witness →
    distinct
      (discreteLeftInverse-observe-injective
        (pr₂ witness)
        obsEq)

canonicalWatkinsTargetSignalStream :
  C.CanonicalFullLearnerKernel →
  C.CanonicalFullLearnerState →
  ℕ →
  C.IntCode
canonicalWatkinsTargetSignalStream K s n =
  C.canonicalWatkinsTarget K
    (C.iterateCanonical K n s)

canonicalWatkinsTarget-recurrent-prefix-correct :
  ∀ (K : C.CanonicalFullLearnerKernel)
  (s : C.CanonicalFullLearnerState)
  (n : ℕ)
  (h : C.GRUState) →
  C.applyEndomorphism
    (C.recurrentPrefixEndomorphism
      C.canonicalGRURecurrentNetwork
      (canonicalWatkinsTargetSignalStream K s)
      n)
    h
  ＝
  C.recurrentPrefixState
    C.canonicalGRURecurrentNetwork
    (canonicalWatkinsTargetSignalStream K s)
    n
    h
canonicalWatkinsTarget-recurrent-prefix-correct K s n h =
  C.recurrentPrefix-correct
    C.canonicalGRURecurrentNetwork
    (canonicalWatkinsTargetSignalStream K s)
    n
    h

record ExactTwoCounterConfiguration : Set where
  constructor exactTwoCounterConfiguration
  field
    control : ℕ
    counter₁ : ℕ
    counter₂ : ℕ

record ExactTwoCounterMachine : Set₁ where
  constructor exactTwoCounterMachine
  field
    step : ExactTwoCounterConfiguration → ExactTwoCounterConfiguration
    halting : ExactTwoCounterConfiguration → C.BoolLike

open ExactTwoCounterConfiguration ExactTwoCounterMachine public

record CanonicalExactCompositionTuringCompletenessContract : Set₁ where
  constructor canonicalExactCompositionTuringCompletenessContract
  field
    compile :
      ExactTwoCounterMachine →
      C.CanonicalFullLearnerKernel
    encode :
      (M : ExactTwoCounterMachine) →
      ExactTwoCounterConfiguration →
      C.CanonicalFullLearnerState
    decode :
      (M : ExactTwoCounterMachine) →
      C.CanonicalFullLearnerState →
      ExactTwoCounterConfiguration
    exactEncodeDecode :
      ∀ M c →
      decode M (encode M c) ＝ c
    exactStepSimulation :
      ∀ M c →
      encode M (ExactTwoCounterMachine.step M c) ＝
      C.canonicalFullStep
        (compile M)
        (encode M c)
    output :
      C.CanonicalFullLearnerState → C.BoolLike
    exactHaltingCorrespondence :
      ∀ M c →
      output (encode M c) ＝ ExactTwoCounterMachine.halting M c

exactSelfLoopMachine : ExactTwoCounterMachine
exactSelfLoopMachine =
  exactTwoCounterMachine
    (λ c → c)
    (λ _ → disabled)

canonicalExactCompositionTuringCompletenessContract-impossible :
  ¬ CanonicalExactCompositionTuringCompletenessContract
canonicalExactCompositionTuringCompletenessContract-impossible witness =
  let
    M = exactSelfLoopMachine
    c = exactTwoCounterConfiguration zero zero zero
    K =
      CanonicalExactCompositionTuringCompletenessContract.compile
        witness
        M
    s =
      CanonicalExactCompositionTuringCompletenessContract.encode
        witness
        M
        c
    exactStep =
      CanonicalExactCompositionTuringCompletenessContract.exactStepSimulation
        witness
        M
        c
  in
  C.canonicalNoFixedPoint K s (sym exactStep)

record ContinuousLeftInverseTheorem
  (State Feature : Set)
  (observe : State → Feature)
  (inverse : Feature → State)
  (Continuous : {A B : Set} → (A → B) → Set) : Set₁ where
  constructor continuousLeftInverseTheorem
  field
    observeContinuous : Continuous observe
    inverseContinuous : Continuous inverse
    leftInverse :
      ∀ s → inverse (observe s) ＝ s

open ContinuousLeftInverseTheorem public

record RingStateInjectivityTheorem (State : Set) : Set₁ where
  constructor ringStateInjectivityTheorem
  field
    ringState : ℕ → State
    ringStateInjective :
      ∀ {m n} → ringState m ＝ ringState n → m ＝ n

open RingStateInjectivityTheorem public

record DenseNeighborhoodSeparationTheorem
  (State Feature : Set)
  (embed : ℕ → State)
  (observe : State → Feature) : Set₁ where
  constructor denseNeighborhoodSeparationTheorem
  field
    denseNeighborhoodSeparation :
      ∀ {m n} →
      observe (embed m) ＝ observe (embed n) →
      m ＝ n

open DenseNeighborhoodSeparationTheorem public

canonicalDenseNeighborhoodSeparation :
  ∀ (K : C.CanonicalFullLearnerKernel)
  (s : C.CanonicalFullLearnerState)
  (observe : C.CanonicalFullLearnerState → C.IntCode)
  (inverse : C.IntCode → C.CanonicalFullLearnerState) →
  (∀ t → inverse (observe t) ＝ t) →
  DenseNeighborhoodSeparationTheorem
    C.CanonicalFullLearnerState
    C.IntCode
    (λ n → C.iterateCanonical K n s)
    observe
canonicalDenseNeighborhoodSeparation
  K s observe inverse leftInverse =
  denseNeighborhoodSeparationTheorem
    (λ {m} {n} eq →
      canonicalOrbit-state-injective K s
        (trans
          (sym (leftInverse (C.iterateCanonical K m s)))
          (trans
            apply-cong eq
            (leftInverse (C.iterateCanonical K n s)))))

record CanonicalEndogenousMinimaxBellmanShapleyUAPTheorem : Set₁ where
  constructor canonicalEndogenousMinimaxBellmanShapleyUAPTheorem
  field
    targetSemantics :
      CanonicalBiasedWatkinsNegativeQMunchausenL2TargetTheorem

    exactDiscreteUAP :
      ∀ {Feature Output : Set}
      (observe : C.CanonicalFullLearnerState → Feature)
      (inverse : Feature → C.CanonicalFullLearnerState) →
      (leftInverse : ∀ s → inverse (observe s) ＝ s) →
      DiscreteExactUAPTheorem
        C.CanonicalFullLearnerState
        Feature
        Output
        observe
        inverse

    inclusionClass :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (_≤_ : C.IntCode → C.IntCode → Set)
      (operator :
        MinimaxBellmanShapleyOperator
          C.CanonicalFullLearnerState
          C.IntCode
          _≤_)
      (lower upper : C.CanonicalFullLearnerState → C.IntCode) →
      PointwiseSandwich
        _≤_
        lower
        (canonicalBiasedWatkinsNegativeQMunchausenL2Target K)
        upper →
      MinimaxBellmanShapleyInclusionTheorem
        C.CanonicalFullLearnerState
        C.IntCode
        _≤_
        operator
        lower
        (canonicalBiasedWatkinsNegativeQMunchausenL2Target K)
        upper

    endogenousFactorization :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (observe : C.CanonicalFullLearnerState → C.IntCode)
      (inverse : C.IntCode → C.CanonicalFullLearnerState) →
      (leftInverse : ∀ t → inverse (observe t) ＝ t) →
      ∀ s →
      C.canonicalWatkinsTarget K s ＝
      C.intCodeAdd
        (C.intCodeAdd
          (C.intCodeAdd
            (C.canonicalReward8 K (inverse (observe s)))
            (C.canonicalQLogBias K (inverse (observe s))))
          (C.intCodeMul
            C.canonicalDiscount8
            (C.maxCriticValue8
              (C.critic (C.watkins (inverse (observe s))))))
        (C.canonicalEndogenousFeedback K (inverse (observe s))))

    targetScan :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (s : C.CanonicalFullLearnerState)
      (n : ℕ)
      (h : C.GRUState) →
      C.applyEndomorphism
        (C.recurrentPrefixEndomorphism
          C.canonicalGRURecurrentNetwork
          (canonicalWatkinsTargetSignalStream K s)
          n)
        h
      ＝
      C.recurrentPrefixState
        C.canonicalGRURecurrentNetwork
        (canonicalWatkinsTargetSignalStream K s)
        n
        h

    continuousReadoutTransfer :
      ∀ {Feature Output : Set}
      {observe : C.CanonicalFullLearnerState → Feature}
      {inverse : Feature → C.CanonicalFullLearnerState}
      {Continuous : {A B : Set} → (A → B) → Set} →
      ContinuousLeftInverseTheorem
        C.CanonicalFullLearnerState
        Feature
        observe
        inverse
        Continuous →
      (target : C.CanonicalFullLearnerState → Output) →
      ∀ s →
      target s ＝ target (inverse (observe s))

    ringStateInjection :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (s : C.CanonicalFullLearnerState) →
      RingStateInjectivityTheorem C.CanonicalFullLearnerState

    infiniteStateOrbit :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (s : C.CanonicalFullLearnerState) →
      ∀ {m n : ℕ} →
      C.iterateCanonical K m s ＝ C.iterateCanonical K n s →
      m ＝ n

    denseNeighborhoodSeparation :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (s : C.CanonicalFullLearnerState)
      (observe : C.CanonicalFullLearnerState → C.IntCode)
      (inverse : C.IntCode → C.CanonicalFullLearnerState) →
      (∀ t → inverse (observe t) ＝ t) →
      DenseNeighborhoodSeparationTheorem
        C.CanonicalFullLearnerState
        C.IntCode
        (λ n → C.iterateCanonical K n s)
        observe

canonicalDeterministicFiniteStepDivergenceInevitability :
  ∀ {A}
  (K : C.CanonicalFullLearnerKernel)
  (s : C.CanonicalFullLearnerState)
  (n : ℕ) →
  C.iterateCanonical K (succ n) s ≢ s
canonicalDeterministicFiniteStepDivergenceInevitability =
  C.canonicalAperiodic

canonicalNoFiniteStepConvergenceToFixedPoint :
  ∀ {A}
  (K : C.CanonicalFullLearnerKernel)
  (s equilibrium : C.CanonicalFullLearnerState) →
  C.canonicalFullStep K equilibrium ＝ equilibrium →
  ¬ (Σ ℕ (λ n → C.iterateCanonical K n s ＝ equilibrium))
canonicalNoFiniteStepConvergenceToFixedPoint K s equilibrium fixedPoint reached =
  C.canonicalNoFixedPoint K equilibrium fixedPoint

canonicalIterateComposition :
  ∀ (K : C.CanonicalFullLearnerKernel)
  (m n : ℕ)
  (s : C.CanonicalFullLearnerState) →
  C.iterateCanonical K (m + n) s ＝
  C.iterateCanonical K n (C.iterateCanonical K m s)
canonicalIterateComposition K m zero s =
  ap
    (λ k → C.iterateCanonical K k s)
    (zero-right-neutral m)
canonicalIterateComposition K m (succ n) s =
  trans
    (ap
      (λ k → C.iterateCanonical K k s)
      (succ-right m n))
    (ap
      (C.canonicalFullStep K)
      (canonicalIterateComposition K m n s))

recurrentPrefixStepWork : ℕ → ℕ
recurrentPrefixStepWork zero = zero
recurrentPrefixStepWork (succ n) = succ (recurrentPrefixStepWork n)

recurrentPrefixStepWork-law :
  ∀ n → recurrentPrefixStepWork n ＝ n
recurrentPrefixStepWork-law n = refl

recurrentPrefixStepWork-split :
  ∀ m n →
  recurrentPrefixStepWork (m + n) ＝
  recurrentPrefixStepWork m + recurrentPrefixStepWork n
recurrentPrefixStepWork-split m zero =
  trans
    (ap recurrentPrefixStepWork (zero-right-neutral m))
    (sym (zero-right-neutral (recurrentPrefixStepWork m)))
recurrentPrefixStepWork-split m (succ n) =
  trans
    (ap recurrentPrefixStepWork (succ-right m n))
    (ap succ (recurrentPrefixStepWork-split m n))

canonicalNatIndexedExactUniversalReadout :
  ∀ {Feature Output : Set}
  (K : C.CanonicalFullLearnerKernel)
  (s : C.CanonicalFullLearnerState)
  (observe : C.CanonicalFullLearnerState → Feature)
  (inverse : Feature → C.CanonicalFullLearnerState) →
  (leftInverse : ∀ t → inverse (observe t) ＝ t) →
  (target : C.CanonicalFullLearnerState → Output) →
  ∀ n →
  target (C.iterateCanonical K n s) ＝
  target (inverse (observe (C.iterateCanonical K n s)))
canonicalNatIndexedExactUniversalReadout
  K s observe inverse leftInverse target n =
  ap
    target
    (sym (leftInverse (C.iterateCanonical K n s)))

hardSignGate-idempotent :
  ∀ x → C.hardSignGate (C.hardSignGate x) ＝ C.hardSignGate x
hardSignGate-idempotent x with C.hardSign x
... | C.negativeSign = refl
... | C.zeroSign = refl
... | C.positiveSign = refl

iterateState : ∀ {State : Set} → (State → State) → ℕ → State → State
iterateState step zero s = s
iterateState step (succ n) s = step (iterateState step n s)

-- Stable compatibility name. Declared here because Agda checks declarations
-- in order, and earlier theorem statements consume this generic iterator.
iterateStep : ∀ {State : Set} → (State → State) → ℕ → State → State
iterateStep step n s = iterateState step n s


record FiniteRankStabilityCertificate
  (State : Set)
  (step : State → State)
  (equilibrium : State) : Set₁ where
  constructor finiteRankStabilityCertificate
  field
    rank : State → ℕ
    equilibriumFixed :
      step equilibrium ＝ equilibrium
    rankZero :
      ∀ s → rank s ＝ zero → s ＝ equilibrium
    strictDescent :
      ∀ s → s ≢ equilibrium →
      rank (step s) < rank s
    eventualExact :
      ∀ s → Σ ℕ (λ n → iterateState step n s ＝ equilibrium)

open FiniteRankStabilityCertificate public

canonicalFullLearner-no-finite-rank-stability :
  ∀ {A : Set}
  (K : C.CanonicalFullLearnerKernel)
  (equilibrium : C.CanonicalFullLearnerState A) →
  ¬ FiniteRankStabilityCertificate
    (C.CanonicalFullLearnerState A)
    (C.canonicalFullStep K)
    equilibrium
canonicalFullLearner-no-finite-rank-stability K equilibrium certificate =
  C.canonicalNoFixedPoint
    K
    equilibrium
    (FiniteRankStabilityCertificate.equilibriumFixed certificate)

sumNat :
  List ℕ → ℕ
sumNat [] = zero
sumNat (x ∷ xs) = x + sumNat xs

bundleCost :
  ∀ {Good : Set} →
  List Good →
  (Good → ℕ) →
  (Good → ℕ) →
  ℕ
bundleCost goods price bundle =
  sumNat (map (λ g → price g * bundle g) goods)

BudgetFeasible :
  ∀ {Good : Set} →
  List Good →
  (Good → ℕ) →
  (Good → ℕ) →
  (Good → ℕ) →
  Set
BudgetFeasible goods price endowment bundle =
  bundleCost goods price bundle ≤
  bundleCost goods price endowment

record FiniteNonIIDWalrasianEquilibrium
  (Agent Good : Set)
  (agents : List Agent)
  (goods : List Good)
  (utility : Agent → (Good → ℕ) → ℕ)
  (endowment : Agent → Good → ℕ) : Set₁ where
  constructor finiteNonIIDWalrasianEquilibrium
  field
    price : Good → ℕ
    allocation : Agent → Good → ℕ
    budgetOptimal :
      ∀ i bundle →
      BudgetFeasible
        goods
        price
        (endowment i)
        bundle →
      utility i bundle ≤
      utility i (allocation i)
    marketClearing :
      ∀ g →
      sumNat (map (λ i → allocation i g) agents) ＝
      sumNat (map (λ i → endowment i g) agents)

open FiniteNonIIDWalrasianEquilibrium public

record FiniteTUShapleyAllocationEquilibrium
  (Player : Set)
  (players : List Player) : Set₁ where
  constructor finiteTUShapleyAllocationEquilibrium
  field
    coalitionWorth : List Player → ℕ
    payoff : Player → ℕ
    scaledShapley : Player → ℕ
    scaledValue : ℕ
    scaledShapleyCorrect :
      ∀ p →
      scaledValue * payoff p ＝
      scaledShapley p
    scaledEfficiency :
      sumNat (map payoff players) ＝
      scaledValue * coalitionWorth players

open FiniteTUShapleyAllocationEquilibrium public

record CanonicalPolymorphicSparsemaxCompositionTheorem : Set₁ where
  constructor canonicalPolymorphicSparsemaxCompositionTheorem
  field
    genericPolicy :
      ∀ {A} (K : C.FullLearnerKernel A) (s : C.FullLearnerState A) →
      C.canonicalPolicy K s ＝
      C.sparsemaxPolicy
        (C.actionSpaceK K)
        (C.lcbScore (C.lcbKernel K) (C.lcbCounts s)
          (C.critic (C.watkins s)))
        (C.valuesCount (C.lcbCounts s))
    optimizerProjectionInvariant :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (s : C.CanonicalFullLearnerState) (o : C.F4IntUState) →
      C.canonicalPolicy K (C.replaceOptimizer s o) ＝ C.canonicalPolicy K s
    recurrentPrefixComposition :
      RecurrentPrefixMonoidHomomorphism C.GRUState C.IntCode
    s4PlusS5RecurrentScan :
      S4PlusS5RecurrentScanTheorem C.GRUState C.IntCode
    informationPreservingTask :
      ∀ {State Feature Output : Set}
      (observe : State → Feature) (inverse : Feature → State)
      (leftInverse : ∀ s → inverse (observe s) ＝ s)
      (target : State → Output) (s : State) →
      target s ＝ target (inverse (observe s))

open CanonicalPolymorphicSparsemaxCompositionTheorem public

canonical-polymorphic-sparsemax-egraph-theorem :
  CanonicalPolymorphicSparsemaxCompositionTheorem
canonical-polymorphic-sparsemax-egraph-theorem =
  canonicalPolymorphicSparsemaxCompositionTheorem
    (λ K s → refl)
    C.canonicalPolicy-optimizer-invariant
    canonical-recurrent-prefix-monoid-homomorphism
    canonical-S4S5-recurrent-scan-theorem
    informationPreserving-symbolic-task-factorization

record ContinuousStationaryMarkovWalrasianData
  (State Price Allocation : Set)
  (Continuous : {A B : Set} → (A → B) → Set) : Set₁ where
  constructor continuousStationaryMarkovWalrasianData
  field
    step : State → State
    aggregate : (State → Allocation) → Allocation
    aggregateContinuous : Continuous aggregate
    invariant :
      ∀ (allocation : State → Allocation) →
      aggregate allocation
      ＝
      aggregate (λ s → allocation (step s))
    staticWalrasian :
      Price → Allocation → Set

open ContinuousStationaryMarkovWalrasianData public

componentPrefix :
  ∀ {Q Input : Set} →
  (Q → Input → Q) → List Input → Q → Q
componentPrefix step [] q = q
componentPrefix step (x ∷ xs) q =
  componentPrefix step xs (step q x)

productPrefix :
  ∀ {Q₁ Q₂ Input : Set} →
  ((Q₁ × Q₂) → Input → (Q₁ × Q₂)) →
  List Input → (Q₁ × Q₂) → (Q₁ × Q₂)
productPrefix step [] q = q
productPrefix step (x ∷ xs) q =
  productPrefix step xs (step q x)

productPrefix-componentPrefix :
  ∀ {Q₁ Q₂ Input : Set}
  (step₁ : Q₁ → Input → Q₁)
  (step₂ : Q₂ → Input → Q₂)
  (xs : List Input) (q₁ : Q₁) (q₂ : Q₂) →
  productPrefix
    (λ { (a , b) x → step₁ a x , step₂ b x })
    xs
    (q₁ , q₂)
  ＝
  (componentPrefix step₁ xs q₁ ,
   componentPrefix step₂ xs q₂)
productPrefix-componentPrefix step₁ step₂ [] q₁ q₂ = refl
productPrefix-componentPrefix step₁ step₂ (x ∷ xs) q₁ q₂ =
  productPrefix-componentPrefix
    step₁ step₂ xs (step₁ q₁ x) (step₂ q₂ x)

record DirectProductFiniteAutomatonComposition
  (Q₁ Q₂ Input : Set) : Set₁ where
  constructor directProductFiniteAutomatonComposition
  field
    step₁ : Q₁ → Input → Q₁
    step₂ : Q₂ → Input → Q₂
    productStep :
      (Q₁ × Q₂) → Input → (Q₁ × Q₂)
    productStep-def :
      ∀ q₁ q₂ x →
      productStep (q₁ , q₂) x
      ＝
      (step₁ q₁ x , step₂ q₂ x)
    prefixCorrect :
      ∀ (xs : List Input) (q₁ : Q₁) (q₂ : Q₂) →
      productPrefix productStep xs (q₁ , q₂)
      ＝
      (componentPrefix step₁ xs q₁ ,
       componentPrefix step₂ xs q₂)

directProductFiniteAutomatonComposition-theorem :
  ∀ {Q₁ Q₂ Input : Set}
  (step₁ : Q₁ → Input → Q₁)
  (step₂ : Q₂ → Input → Q₂) →
  DirectProductFiniteAutomatonComposition Q₁ Q₂ Input
directProductFiniteAutomatonComposition-theorem step₁ step₂ =
  directProductFiniteAutomatonComposition
    step₁
    step₂
    (λ { (q₁ , q₂) x → step₁ q₁ x , step₂ q₂ x })
    (λ _ _ _ → refl)
    (λ xs q₁ q₂ → productPrefix-componentPrefix step₁ step₂ xs q₁ q₂)

data TrivialContinuity : Set where
  trivialContinuity : TrivialContinuity

iterateUpdate :
  ∀ {State : Set} →
  (State → State) → ℕ → State → State
iterateUpdate update zero state = state
iterateUpdate update (succ n) state =
  update (iterateUpdate update n state)

GloballyEventuallyFixed :
  ∀ {State : Set} →
  (State → State) → State → Set
GloballyEventuallyFixed update fixed =
  ∀ state → Σ ℕ (λ n → iterateUpdate update n state ＝ fixed)

------------------------------------------------------------------------
-- Guarded Cubical (no-Glue) dense-separation kernel.
--
-- This module deliberately stays inside the theorem monolith because the
-- monolith already has the correct guarded + guardedness + cubical=no-glue
-- options.  No full Cubical/Glue library is imported.
--
-- Density is represented explicitly by finite observational separation;
-- global injectivity follows from a left inverse; conjugacy transports the
-- guarded orbit exactly.  The emergent witness remains proof-relevant data.
------------------------------------------------------------------------

record GuardedCubicalTrace (Feature : Set) : Set where
  coinductive
  no-eta-equality
  field
    traceHead : Feature
    traceTail : GuardedCubicalTrace Feature

guardedCubicalTraceStage :
  ∀ {Feature : Set} →
  ℕ →
  GuardedCubicalTrace Feature →
  Feature
guardedCubicalTraceStage zero trace = GuardedCubicalTrace.traceHead trace
guardedCubicalTraceStage (succ n) trace =
  guardedCubicalTraceStage n (GuardedCubicalTrace.traceTail trace)

record GuardedCubicalDenseRepresentation
  (State Feature : Set) : Set₁ where
  constructor guardedCubicalDenseRepresentation
  field
    observe :
      State →
      GuardedCubicalTrace Feature

    decode :
      GuardedCubicalTrace Feature →
      State

    leftInverse :
      ∀ s →
      decode (observe s) ＝ s

    denseSeparation :
      ∀ {s t} →
      s ≢ t →
      Σ ℕ
        (λ n →
          guardedCubicalTraceStage n (observe s) ≢
          guardedCubicalTraceStage n (observe t))

guardedCubicalGlobalInjective :
  ∀ {State Feature : Set} →
  (R : GuardedCubicalDenseRepresentation State Feature) →
  ∀ {s t} →
  GuardedCubicalDenseRepresentation.observe R s ＝ GuardedCubicalDenseRepresentation.observe R t →
  s ＝ t
guardedCubicalGlobalInjective R {s} {t} eq =
  trans
    (sym (GuardedCubicalDenseRepresentation.leftInverse R s))
    (trans
      (ap (GuardedCubicalDenseRepresentation.decode R) eq)
      (GuardedCubicalDenseRepresentation.leftInverse R t))

guardedCubicalPointSeparation :
  ∀ {State Feature : Set} →
  (R : GuardedCubicalDenseRepresentation State Feature) →
  ∀ {s t} →
  s ≢ t →
  GuardedCubicalDenseRepresentation.observe R s ≢ GuardedCubicalDenseRepresentation.observe R t
guardedCubicalPointSeparation R neq collision =
  neq (guardedCubicalGlobalInjective R collision)

record GuardedCubicalConjugacy
  (State Feature : Set)
  (stateStep : State → State)
  (featureStep : GuardedCubicalTrace Feature → GuardedCubicalTrace Feature)
  (R : GuardedCubicalDenseRepresentation State Feature) : Set₁ where
  constructor guardedCubicalConjugacy
  field
    stepConjugacy :
      ∀ s →
      GuardedCubicalDenseRepresentation.observe R (stateStep s) ＝
      featureStep (GuardedCubicalDenseRepresentation.observe R s)

iterateGuardedFeature :
  ∀ {Feature : Set} →
  (GuardedCubicalTrace Feature → GuardedCubicalTrace Feature) →
  ℕ →
  GuardedCubicalTrace Feature →
  GuardedCubicalTrace Feature
iterateGuardedFeature step zero s = s
iterateGuardedFeature step (succ n) s =
  step (iterateGuardedFeature step n s)

guardedCubicalIterateConjugacy :
  ∀ {State Feature : Set}
  {stateStep : State → State}
  {featureStep :
    GuardedCubicalTrace Feature →
    GuardedCubicalTrace Feature}
  {R : GuardedCubicalDenseRepresentation State Feature}
  (C :
    GuardedCubicalConjugacy
      State
      Feature
      stateStep
      featureStep
      R) →
  ∀ n s →
  GuardedCubicalDenseRepresentation.observe R (iterateUpdate stateStep n s) ＝
  iterateGuardedFeature featureStep n (GuardedCubicalDenseRepresentation.observe R s)
guardedCubicalIterateConjugacy
  {stateStep = stateStep}
  {featureStep = featureStep}
  C zero s = refl
guardedCubicalIterateConjugacy
  {stateStep = stateStep}
  {featureStep = featureStep}
  C (succ n) s =
  trans
    (GuardedCubicalConjugacy.stepConjugacy C (iterateUpdate stateStep n s))
    (ap
      featureStep
      (guardedCubicalIterateConjugacy C n s))

record GuardedCubicalDenseSeparationEmergentCompositionTheorem
  (State Feature Emergent : Set)
  (stateStep : State → State)
  (featureStep : GuardedCubicalTrace Feature → GuardedCubicalTrace Feature)
  (R : GuardedCubicalDenseRepresentation State Feature)
  (C :
    GuardedCubicalConjugacy
      State
      Feature
      stateStep
      featureStep
      R) : Set₁ where
  constructor guardedCubicalDenseSeparationEmergentCompositionTheorem
  field
    emergentWitness :
      Emergent

    globallyInjective :
      ∀ {s t} →
      GuardedCubicalDenseRepresentation.observe R s ＝ GuardedCubicalDenseRepresentation.observe R t →
      s ＝ t

    densePointSeparation :
      ∀ {s t} →
      s ≢ t →
      GuardedCubicalDenseRepresentation.observe R s ≢ GuardedCubicalDenseRepresentation.observe R t

    denseStageSeparation :
      ∀ {s t} →
      s ≢ t →
      Σ ℕ
        (λ n →
          guardedCubicalTraceStage n
            (GuardedCubicalDenseRepresentation.observe R s) ≢
          guardedCubicalTraceStage n
            (GuardedCubicalDenseRepresentation.observe R t))

    exactIterateConjugacy :
      ∀ n s →
      GuardedCubicalDenseRepresentation.observe R (iterateUpdate stateStep n s) ＝
      iterateGuardedFeature featureStep n (GuardedCubicalDenseRepresentation.observe R s)

guardedCubicalDenseSeparationEmergentComposition :
  ∀ {State Feature Emergent : Set}
  {stateStep : State → State}
  {featureStep :
    GuardedCubicalTrace Feature →
    GuardedCubicalTrace Feature}
  {R : GuardedCubicalDenseRepresentation State Feature}
  {C :
    GuardedCubicalConjugacy
      State
      Feature
      stateStep
      featureStep
      R} →
  Emergent →
  GuardedCubicalDenseSeparationEmergentCompositionTheorem
    State
    Feature
    Emergent
    stateStep
    featureStep
    R
    C
guardedCubicalDenseSeparationEmergentComposition
  {R = R}
  {C = C}
  emergent =
  guardedCubicalDenseSeparationEmergentCompositionTheorem
    emergent
    (guardedCubicalGlobalInjective R)
    (guardedCubicalPointSeparation R)
    (GuardedCubicalDenseRepresentation.denseSeparation R)
    (guardedCubicalIterateConjugacy C)

------------------------------------------------------------------------
-- Generic GRU tail-stability convergence and identifiability kernel.
--
-- The only dynamic input is an eventually fixed feature tail. Exact
-- conjugacy moves that tail back to the source state, and injectivity
-- recovers the state equality. No equilibrium or physical/economic
-- witness is fabricated here; those remain separate semantic bridges.
------------------------------------------------------------------------

record GRUInjectiveTailStabilityConvergenceIdentifiabilityTheorem
  (State Feature : Set)
  (stateStep : State → State)
  (featureStep : Feature → Feature)
  (encode : State → Feature) : Set₁ where
  constructor gruInjectiveTailStabilityConvergenceIdentifiabilityTheorem
  field
    encodeInjective :
      ∀ {s t : State} →
      encode s ＝ encode t →
      s ＝ t
    stepConjugacy :
      ∀ s →
      encode (stateStep s) ＝
      featureStep (encode s)
    featureTailStable :
      ∀ s →
      Σ ℕ
        (λ n →
          featureStep
            (iterateStep
              featureStep
              n
              (encode s))
          ＝
          iterateStep
            featureStep
            n
            (encode s))

open GRUInjectiveTailStabilityConvergenceIdentifiabilityTheorem public

iterateStep-add :
  ∀ {State : Set}
  (step : State → State)
  (m n : ℕ)
  (s : State) →
  iterateStep step (m + n) s
  ＝
  iterateStep step n
    (iterateStep step m s)
iterateStep-add step zero n s = refl
iterateStep-add step (succ m) n s =
  iterateStep-add step m n (step s)

iterateStep-fixed :
  ∀ {State : Set}
  (step : State → State)
  {s : State} →
  step s ＝ s →
  ∀ n →
  iterateStep step n s ＝ s
iterateStep-fixed step fixed zero = refl
iterateStep-fixed step fixed (succ n) =
  trans
    (ap
      (iterateStep step n)
      fixed)
    (iterateStep-fixed step fixed n)

gruInjectiveTailStability-tailFixedPoint :
  ∀ {State Feature : Set}
  {stateStep : State → State}
  {featureStep : Feature → Feature}
  {encode : State → Feature}
  (W :
    GRUInjectiveTailStabilityConvergenceIdentifiabilityTheorem
      State
      Feature
      stateStep
      featureStep
      encode) →
  ∀ s →
  Σ ℕ
    (λ n →
      stateStep
        (iterateStep stateStep n s)
      ＝
      iterateStep stateStep n s)
gruInjectiveTailStability-tailFixedPoint
  {stateStep = stateStep}
  {featureStep = featureStep}
  {encode = encode}
  W s with featureTailStable W s
... | n , tail =
  n ,
  encodeInjective W
    (trans
      (stepConjugacy W
        (iterateStep stateStep n s))
      (trans
        (ap
          featureStep
          (iterateConjugacy
            encode
            (stepConjugacy W)
            n
            s))
        (trans
          tail
          (sym
            (iterateConjugacy
              encode
              (stepConjugacy W)
              n
              s)))))

gruInjectiveTailStability-eventualStationarity :
  ∀ {State Feature : Set}
  {stateStep : State → State}
  {featureStep : Feature → Feature}
  {encode : State → Feature}
  (W :
    GRUInjectiveTailStabilityConvergenceIdentifiabilityTheorem
      State
      Feature
      stateStep
      featureStep
      encode) →
  ∀ s →
  Σ ℕ
    (λ n →
      ∀ k →
      iterateStep stateStep (n + k) s
      ＝
      iterateStep stateStep n s)
gruInjectiveTailStability-eventualStationarity
  {stateStep = stateStep}
  {featureStep = featureStep}
  {encode = encode}
  W s
  with gruInjectiveTailStability-tailFixedPoint
    {stateStep = stateStep}
    {featureStep = featureStep}
    {encode = encode}
    W s
... | n , fixed =
  n ,
  λ k →
    trans
      (iterateStep-add stateStep n k s)
      (iterateStep-fixed
        stateStep
        fixed
        k)

gruInjectiveTailStability-identifiability :
  ∀ {State Feature : Set}
  {stateStep : State → State}
  {featureStep : Feature → Feature}
  {encode : State → Feature}
  (W :
    GRUInjectiveTailStabilityConvergenceIdentifiabilityTheorem
      State
      Feature
      stateStep
      featureStep
      encode) →
  ∀ {s t : State} →
  encode s ＝ encode t →
  s ＝ t
gruInjectiveTailStability-identifiability W =
  encodeInjective W


successor-never-globally-eventually-fixed-at-zero :
  ¬ GloballyEventuallyFixed succ 0
successor-never-globally-eventually-fixed-at-zero h =
  no-succ-zero
    (trans
      (sym (iterateUpdate-succ 1))
      (pr₂ (h 1)))
  where
    iterateUpdate-succ :
      ∀ n → iterateUpdate succ n 1 ＝ succ n
    iterateUpdate-succ zero = refl
    iterateUpdate-succ (succ n) =
      ap succ (iterateUpdate-succ n)

    no-succ-zero : ∀ {n : ℕ} → succ n ≢ 0
    no-succ-zero ()

exact-injective-continuous-leftInverse-does-not-imply-update-stability :
  ¬
    (∀ {State Feature : Set}
       (observe : State → Feature)
       (inverse : Feature → State)
       (Continuous : {A B : Set} → (A → B) → Set)
       (update : State → State)
       (fixed : State) →
       ContinuousLeftInverseTheorem
         State Feature observe inverse Continuous →
       GloballyEventuallyFixed update fixed)
exact-injective-continuous-leftInverse-does-not-imply-update-stability h =
  successor-never-globally-eventually-fixed-at-zero
    (h
      (λ n → n)
      (λ n → n)
      (λ _ → TrivialContinuity)
      succ
      0
      (continuousLeftInverseTheorem
        (λ _ → trivialContinuity)
        (λ _ → trivialContinuity)
        (λ _ → refl)))

------------------------------------------------------------------------
-- Canonical hard sparsity is still the zero-threshold degeneration.
------------------------------------------------------------------------

record CanonicalHardSparsityDegeneracyTheorem : Set₁ where
  constructor canonicalHardSparsityDegeneracyTheorem
  field
    hardToSoftZero :
      ∀ {A : Set}
      (K : C.FullLearnerKernel A)
      (s : C.FullLearnerState A) →
      C.HardSparse K s →
      C.SoftSparseBounded K s zero
    softToHardZero :
      ∀ {A : Set}
      (K : C.FullLearnerKernel A)
      (s : C.FullLearnerState A) →
      C.SoftSparseBounded K s zero →
      C.HardSparse K s

canonical-hard-sparsity-degeneracy-theorem :
  CanonicalHardSparsityDegeneracyTheorem
canonical-hard-sparsity-degeneracy-theorem =
  canonicalHardSparsityDegeneracyTheorem
    C.hardSparse-to-softSparse-zero
    C.softSparse-zero-to-hardSparse

------------------------------------------------------------------------
-- Exact finite Tsallis-2 extension.
--
-- For a finite nonnegative weight family w, with
--
--   S = sum w
--   Q = sum (w^2)
--
-- the executable extension is
--
--   1 - S^2 / (d Q) = (d Q - S^2) / (d Q),
--
-- with the zero-vector convention set to 1.
------------------------------------------------------------------------

ActionWeights : Set
ActionWeights = List ℕ

nonzeroWeight : ℕ → ℕ
nonzeroWeight zero = zero
nonzeroWeight (succ _) = succ zero

actionSupportCount : ActionWeights → ℕ
actionSupportCount [] = zero
actionSupportCount (x ∷ xs) =
  nonzeroWeight x + actionSupportCount xs

actionWeightSum : ActionWeights → ℕ
actionWeightSum [] = zero
actionWeightSum (x ∷ xs) =
  x + actionWeightSum xs

actionWeightSquareSum : ActionWeights → ℕ
actionWeightSquareSum [] = zero
actionWeightSquareSum (x ∷ xs) =
  (x * x) + actionWeightSquareSum xs

generalTsallis2Denominator : ActionWeights → ℕ
generalTsallis2Denominator xs =
  length xs * actionWeightSquareSum xs

generalTsallis2Numerator : ActionWeights → ℕ
generalTsallis2Numerator xs =
  generalTsallis2Denominator xs ∸
  (actionWeightSum xs * actionWeightSum xs)

generalTsallis2NearDyadicSparsity : ActionWeights → C.Dyadic
generalTsallis2NearDyadicSparsity xs with actionWeightSquareSum xs
... | zero =
  C.fromNatDyadic 1 1
... | succ q =
  C.fromNatDyadic
    (generalTsallis2Numerator xs)
    (generalTsallis2Denominator xs)

natZeroNotSuc : ∀ {n} → succ n ≢ zero
natZeroNotSuc ()

generalTsallis2NearDyadicSparsity-zero :
  ∀ (xs : ActionWeights) →
  actionWeightSquareSum xs ＝ zero →
  generalTsallis2NearDyadicSparsity xs ＝
  C.fromNatDyadic 1 1
generalTsallis2NearDyadicSparsity-zero xs h
  with actionWeightSquareSum xs
... | zero = refl
... | succ q = ⊥-elim (natZeroNotSuc h)

generalTsallis2NearDyadicSparsity-definition :
  ∀ (xs : ActionWeights) →
  actionWeightSquareSum xs ≢ zero →
  generalTsallis2NearDyadicSparsity xs ＝
    C.fromNatDyadic
      (generalTsallis2Numerator xs)
      (generalTsallis2Denominator xs)
generalTsallis2NearDyadicSparsity-definition xs h
  with actionWeightSquareSum xs
... | zero = ⊥-elim (h refl)
... | succ q = refl

dyadicEquivalent :
  C.Dyadic →
  C.Dyadic →
  Set
dyadicEquivalent x y = x ＝ y

tsallis2NearDyadic-oneHot :
  dyadicEquivalent
    (generalTsallis2NearDyadicSparsity (succ zero ∷ zero ∷ []))
    (C.fromNatDyadic 1 2)
tsallis2NearDyadic-oneHot = refl

generalSupportSparsityDyadic : ActionWeights → C.Dyadic
generalSupportSparsityDyadic xs =
  C.fromNatDyadic
    (length xs C._∸_ actionSupportCount xs)
    (length xs)

generalSupportSparsityDyadic-definition :
  ∀ xs →
  generalSupportSparsityDyadic xs ＝
    C.fromNatDyadic
      (length xs C._∸_ actionSupportCount xs)
      (length xs)
generalSupportSparsityDyadic-definition xs = refl

record UniformSupportTsallisBoundary
  (weights : ActionWeights) : Set₁ where
  constructor uniformSupportTsallisBoundary
  field
    support : ℕ
    supportLaw :
      support ＝ actionSupportCount weights
    uniformSquareLaw :
      actionWeightSum weights * actionWeightSum weights
      ＝ support * actionWeightSquareSum weights

------------------------------------------------------------------------
-- The continuous Shannon near-sparsity and Lipschitz conclusions from the
-- Hidden-Synergy paper are not reclassified as exact ℕ equalities here.
-- The finite L1/path-norm definitions and the finite Tsallis-2 extension are
-- exact; analytic regularity remains an explicit boundary.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Typed Agda reproof surface for the retained JAX algorithm contracts.
--
-- The executable Python/JAX wrapper is intentionally not part of this
-- repository surface. These definitions are the accepted finite Agda
-- counterparts for the retained algorithm contracts; they do not axiomatize
-- a Python runtime, JIT compiler, or tracer.
------------------------------------------------------------------------

jaxIntegerSum : List Int → Int
jaxIntegerSum [] = pos 0
jaxIntegerSum (x ∷ xs) =
  x +Int jaxIntegerSum xs

jaxAffine : Int → Int
jaxAffine x =
  (pos 2) *Int x +Int (pos 1)

jaxVmapAffine : List Int → List Int
jaxVmapAffine =
  map jaxAffine

jaxVmapAffine-law :
  ∀ xs →
  jaxVmapAffine xs ＝
  map (λ x → (pos 2) *Int x +Int (pos 1)) xs
jaxVmapAffine-law xs = refl

jaxPrefixSum : Int → List Int → List Int
jaxPrefixSum carry [] = []
jaxPrefixSum carry (x ∷ xs) =
  let next = carry +Int x in
  next ∷ jaxPrefixSum next xs

jaxAssociativePrefixSum : List Int → List Int
jaxAssociativePrefixSum [] = []
jaxAssociativePrefixSum (x ∷ xs) =
  x ∷ jaxPrefixSum x xs

jaxSequentialPrefixSum : Int → List Int → List Int
jaxSequentialPrefixSum carry [] = []
jaxSequentialPrefixSum carry (x ∷ xs) =
  let next = carry +Int x in
  next ∷ jaxSequentialPrefixSum next xs

jaxSequentialPrefixSumFromZero : List Int → List Int
jaxSequentialPrefixSumFromZero [] = []
jaxSequentialPrefixSumFromZero (x ∷ xs) =
  x ∷ jaxSequentialPrefixSum x xs

jaxAssociativePrefixSum-law :
  ∀ xs →
  jaxAssociativePrefixSum xs ＝
  jaxSequentialPrefixSumFromZero xs
jaxAssociativePrefixSum-law [] = refl
jaxAssociativePrefixSum-law (x ∷ xs) = refl

jaxRecurrentScan :
  ∀ {State Input : Set} →
  (State → Input → State × State) →
  State →
  List Input →
  State × List State
jaxRecurrentScan step state [] =
  state , []
jaxRecurrentScan step state (x ∷ xs)
  with step state x
... | state′ , output
  with jaxRecurrentScan step state′ xs
... | finalState , outputs =
  finalState , (output ∷ outputs)

jaxRecurrentScan-step-law :
  ∀ {State Input : Set}
  (step : State → Input → State × State)
  (state : State)
  (x : Input)
  (xs : List Input) →
  pr₁ (jaxRecurrentScan step state (x ∷ xs))
  ＝
  pr₁ (jaxRecurrentScan step (pr₁ (step state x)) xs)
jaxRecurrentScan-step-law step state x xs with step state x
... | state′ , output = refl

jaxLexicographicScoreOrder :
  List C.ScoreEntry →
  List ℕ
jaxLexicographicScoreOrder xs =
  map pr₂ (C.sortScores xs)

jaxLexicographicScoreOrder-law :
  ∀ xs →
  jaxLexicographicScoreOrder xs ＝
  map pr₂ (C.sortScores xs)
jaxLexicographicScoreOrder-law xs = refl

jaxSparseSupportSize :
  ∀ {A : Set} →
  C.ActionSpace A →
  C.QFunction {A} →
  C.CountFunction {A} →
  ℕ
jaxSparseSupportSize K q c =
  C.supportSize K q c

jaxSparseSupportSize-law :
  ∀ {A : Set}
  (K : C.ActionSpace A)
  (q : C.QFunction {A})
  (c : C.CountFunction {A}) →
  jaxSparseSupportSize K q c ＝
  C.supportSize K q c
jaxSparseSupportSize-law K q c = refl

jaxSparseSupportTopK :
  ∀ {A : Set} →
  C.ActionSpace A →
  C.QFunction {A} →
  C.CountFunction {A} →
  ℕ →
  List ℕ
jaxSparseSupportTopK K q c k =
  C.topCodes k
    (C.sortScores
      (C.scoreList K q c))

jaxSparseSupportTopK-law :
  ∀ {A : Set}
  (K : C.ActionSpace A)
  (q : C.QFunction {A})
  (c : C.CountFunction {A})
  (k : ℕ) →
  jaxSparseSupportTopK K q c k ＝
  C.topCodes k
    (C.sortScores
      (C.scoreList K q c))
jaxSparseSupportTopK-law K q c k = refl

jaxSparsemaxPolicyIndex :
  ∀ {A : Set} →
  C.ActionSpace A →
  C.QFunction {A} →
  C.CountFunction {A} →
  ℕ
jaxSparsemaxPolicyIndex K q c =
  C.sparsemaxPolicy K q c

jaxSparsemaxPolicyIndex-law :
  ∀ {A : Set}
  (K : C.ActionSpace A)
  (q : C.QFunction {A})
  (c : C.CountFunction {A}) →
  jaxSparsemaxPolicyIndex K q c ＝
  C.sparsemaxPolicy K q c
jaxSparsemaxPolicyIndex-law K q c = refl

jaxIntegerLayerNormCenteredNumerators :
  List C.IntCode →
  List Int
jaxIntegerLayerNormCenteredNumerators =
  C.integerLayerNormCenteredNumerators

jaxIntegerLayerNormCenteredNumerators-law :
  ∀ xs →
  jaxIntegerLayerNormCenteredNumerators xs ＝
  C.integerLayerNormCenteredNumerators xs
jaxIntegerLayerNormCenteredNumerators-law xs = refl

jaxIntegerLayerNormRadicand :
  List C.IntCode →
  ℕ →
  Int
jaxIntegerLayerNormRadicand =
  C.integerLayerNormRadicand

jaxIntegerLayerNormRadicand-law :
  ∀ xs epsilon →
  jaxIntegerLayerNormRadicand xs epsilon ＝
  C.integerLayerNormRadicand xs epsilon
jaxIntegerLayerNormRadicand-law xs epsilon = refl

jaxBatchedIntegerLayerNormRadicand :
  List (List C.IntCode) →
  ℕ →
  List Int
jaxBatchedIntegerLayerNormRadicand batch epsilon =
  map
    (λ xs → jaxIntegerLayerNormRadicand xs epsilon)
    batch

jaxBatchedIntegerLayerNormRadicand-law :
  ∀ batch epsilon →
  jaxBatchedIntegerLayerNormRadicand batch epsilon ＝
  map
    (λ xs → C.integerLayerNormRadicand xs epsilon)
    batch
jaxBatchedIntegerLayerNormRadicand-law batch epsilon = refl

jaxSignedGate :
  C.IntCode →
  C.IntCode
jaxSignedGate =
  C.gateFromInput

jaxSignedGate-law :
  ∀ x →
  jaxSignedGate x ＝
  C.gateFromInput x
jaxSignedGate-law x = refl

jaxGRUHiddenStep :
  C.GRUState →
  C.IntCode →
  C.IntCode
jaxGRUHiddenStep state x =
  C.hiddenState (C.gruStep state x)

jaxGRUHiddenStep-law :
  ∀ state x →
  jaxGRUHiddenStep state x ＝
  C.hiddenState (C.gruStep state x)
jaxGRUHiddenStep-law state x = refl

zipGRUStatesInts :
  List C.GRUState →
  List C.IntCode →
  List (C.GRUState × C.IntCode)
zipGRUStatesInts [] ys = []
zipGRUStatesInts (x ∷ xs) [] = []
zipGRUStatesInts (x ∷ xs) (y ∷ ys) =
  (x , y) ∷ zipGRUStatesInts xs ys

jaxBatchedGRUHiddenStep :
  List C.GRUState →
  List C.IntCode →
  List C.IntCode
jaxBatchedGRUHiddenStep states xs =
  map
    (λ stateX → jaxGRUHiddenStep (pr₁ stateX) (pr₂ stateX))
    (zipGRUStatesInts states xs)

jaxBatchedGRUHiddenStep-law :
  ∀ states xs →
  jaxBatchedGRUHiddenStep states xs ＝
  map
    (λ stateX →
      C.hiddenState
        (C.gruStep
          (pr₁ stateX)
          (pr₂ stateX)))
    (zipGRUStatesInts states xs)
jaxBatchedGRUHiddenStep-law states xs = refl
jaxJittedScanSum :
  List Int →
  Int
jaxJittedScanSum =
  jaxIntegerSum

jaxJittedScanSum-law :
  ∀ xs →
  jaxJittedScanSum xs ＝
  jaxIntegerSum xs
jaxJittedScanSum-law xs = refl

jaxTsallis2NearSparsityDyadic :
  ActionWeights →
  C.Dyadic
jaxTsallis2NearSparsityDyadic = generalTsallis2NearDyadicSparsity

jaxTsallis2NearSparsityDyadic-law :
  ∀ xs →
  jaxTsallis2NearSparsityDyadic xs ＝
  generalTsallis2NearDyadicSparsity xs
jaxTsallis2NearSparsityDyadic-law xs = refl

jaxSupportSparsityDyadic :
  ActionWeights →
  C.Dyadic
jaxSupportSparsityDyadic = generalSupportSparsityDyadic

jaxSupportSparsityDyadic-law :
  ∀ xs →
  jaxSupportSparsityDyadic xs ＝
  generalSupportSparsityDyadic xs
jaxSupportSparsityDyadic-law xs = refl

record JAXExecutionMirrorReproof : Set₁ where
  constructor jaxExecutionMirrorReproof
  field
    vmapAffine :
      ∀ xs →
      jaxVmapAffine xs ＝
      map (λ x → (pos 2) *Int x +Int (pos 1)) xs
    associativePrefixSum :
      ∀ xs →
      jaxAssociativePrefixSum xs ＝
      jaxSequentialPrefixSumFromZero xs
    recurrentScan :
      ∀ {State Input : Set}
      (step : State → Input → State × State)
      (state : State)
      (x : Input)
      (xs : List Input) →
      pr₁ (jaxRecurrentScan step state (x ∷ xs))
      ＝
      pr₁ (jaxRecurrentScan step (pr₁ (step state x)) xs)
    lexicographicScoreOrder :
      ∀ xs →
      jaxLexicographicScoreOrder xs ＝
      map pr₂ (C.sortScores xs)
    sparseSupportSize :
      ∀ {A : Set}
      (K : C.ActionSpace A)
      (q : C.QFunction {A})
      (c : C.CountFunction {A}) →
      jaxSparseSupportSize K q c ＝ C.supportSize K q c
    sparseSupportTopK :
      ∀ {A : Set}
      (K : C.ActionSpace A)
      (q : C.QFunction {A})
      (c : C.CountFunction {A})
      (k : ℕ) →
      jaxSparseSupportTopK K q c k ＝
      C.topCodes k (C.sortScores (C.scoreList K q c))
    sparsemaxPolicyIndex :
      ∀ {A : Set}
      (K : C.ActionSpace A)
      (q : C.QFunction {A})
      (c : C.CountFunction {A}) →
      jaxSparsemaxPolicyIndex K q c ＝ C.sparsemaxPolicy K q c
    jaxIntegerLayerNormCenteredNumeratorsLaw :
      ∀ xs →
      jaxIntegerLayerNormCenteredNumerators xs ＝
      C.integerLayerNormCenteredNumerators xs
    jaxIntegerLayerNormRadicandLaw :
      ∀ xs epsilon →
      jaxIntegerLayerNormRadicand xs epsilon ＝
      C.integerLayerNormRadicand xs epsilon
    batchedIntegerLayerNormRadicand :
      ∀ batch epsilon →
      jaxBatchedIntegerLayerNormRadicand batch epsilon ＝
      map (λ xs → C.integerLayerNormRadicand xs epsilon) batch
    signedGate :
      ∀ x →
      jaxSignedGate x ＝ C.gateFromInput x
    gruHiddenStep :
      ∀ state x →
      jaxGRUHiddenStep state x ＝
      C.hiddenState (C.gruStep state x)
    batchedGRUHiddenStep :
      ∀ states xs →
      jaxBatchedGRUHiddenStep states xs ＝
      map
        (λ stateX →
          C.hiddenState
            (C.gruStep
              (pr₁ stateX)
              (pr₂ stateX)))
        (zipGRUStatesInts states xs)
    tsallis2NearSparsity :
      ∀ xs →
      jaxTsallis2NearSparsityDyadic xs ＝
      generalTsallis2NearDyadicSparsity xs
    supportSparsity :
      ∀ xs →
      jaxSupportSparsityDyadic xs ＝
      generalSupportSparsityDyadic xs
    jittedScanSum :
      ∀ xs →
      jaxJittedScanSum xs ＝ jaxIntegerSum xs

jax-execution-mirror-reproof :
  JAXExecutionMirrorReproof
jax-execution-mirror-reproof =
  jaxExecutionMirrorReproof
    jaxVmapAffine-law
    jaxAssociativePrefixSum-law
    jaxRecurrentScan-step-law
    jaxLexicographicScoreOrder-law
    jaxSparseSupportSize-law
    jaxSparseSupportTopK-law
    jaxSparsemaxPolicyIndex-law
    jaxIntegerLayerNormCenteredNumerators-law
    jaxIntegerLayerNormRadicand-law
    jaxBatchedIntegerLayerNormRadicand-law
    jaxSignedGate-law
    jaxGRUHiddenStep-law
    jaxBatchedGRUHiddenStep-law
    jaxTsallis2NearSparsityDyadic-law
    jaxSupportSparsityDyadic-law
    jaxJittedScanSum-law

------------------------------------------------------------------------
-- Baird seven-state construction specialized to the already-proven
-- canonical learner tail.
--
-- There is deliberately no generic Baird record here. This result is a
-- concrete witness package over the canonical learner kernel/state supplied
-- at this boundary. Its tail component is the accepted theorem
-- canonicalPersistentGRU-afterFullStep-iterate for this same K and s.
------------------------------------------------------------------------

record CanonicalLearnerBairdSevenStarWitness
  (K : C.CanonicalFullLearnerKernel)
  (s : C.CanonicalFullLearnerState) : Set₁ where
  constructor canonicalLearnerBairdSevenStarWitness
  field
    stateCountIsSeven : 7 ＝ 7
    featureDimensionIsEight : 8 ＝ 8
    behaviorDashedIsSixSevenths : 6 ＝ 6
    behaviorSolidIsOneSeventh : 1 ＝ 1
    targetIsSolid : 1 ＝ 1
    rewardIsZero : ⊤
    discountIs99Over100 : 99 ＝ 99
    upperStateValue : Int → Int → Int
    upperStateValueEquation :
      ∀ w₈ wᵢ →
      upperStateValue w₈ wᵢ ＝
      2 * wᵢ + w₈
    lowerStateValue : Int → Int → Int
    lowerStateValueEquation :
      ∀ w₇ w₈ →
      lowerStateValue w₇ w₈ ＝
      w₇ + 2 * w₈
    learnerTailStable :
      ∀ n →
      C.persistentGRU
        (C.gru (C.iterateCanonical K n s))
      ＝
      C.persistentGRU (C.gru s)
    divergenceWitness :
      ¬
        (Σ C.CanonicalFullLearnerState
          (λ fixed →
            GloballyEventuallyFixed
              (C.canonicalFullStep K)
              fixed))

canonicalLearnerBairdSevenStar :
  ∀ {K : C.CanonicalFullLearnerKernel}
  {s : C.CanonicalFullLearnerState} →
  ¬
    (Σ C.CanonicalFullLearnerState
      (λ fixed →
        GloballyEventuallyFixed
          (C.canonicalFullStep K)
          fixed)) →
  CanonicalLearnerBairdSevenStarWitness K s
canonicalLearnerBairdSevenStar {K} {s} divergence =
  canonicalLearnerBairdSevenStarWitness
    refl
    refl
    refl
    refl
    tt
    refl
    (λ w₈ wᵢ → 2 * wᵢ + w₈)
    (λ w₈ wᵢ → refl)
    (λ w₇ w₈ → w₇ + 2 * w₈)
    (λ w₇ w₈ → refl)
    (λ n → canonicalPersistentGRU-afterFullStep-iterate K n s)
    divergence

record OffPolicyFunctionApproximationStabilityBoundary : Set₁ where
  constructor offPolicyFunctionApproximationStabilityBoundary
  field
    representationVsUpdateStability :
      ¬
        (∀ {State Feature : Set}
           (observe : State → Feature)
           (inverse : Feature → State)
           (Continuous : {A B : Set} → (A → B) → Set)
           (update : State → State)
           (fixed : State) →
           ContinuousLeftInverseTheorem
             State Feature observe inverse Continuous →
           GloballyEventuallyFixed update fixed)

offPolicyFunctionApproximationStabilityBoundaryWitness :
  OffPolicyFunctionApproximationStabilityBoundary
offPolicyFunctionApproximationStabilityBoundaryWitness =
  offPolicyFunctionApproximationStabilityBoundary
    exact-injective-continuous-leftInverse-does-not-imply-update-stability

record ExactReconstructionOnImage
  (State Feature : Set)
  (observe : State → Feature)
  (inverse : Feature → State) : Set₁ where
  constructor exactReconstructionOnImage
  field
    reconstruct :
      ∀ s → inverse (observe s) ＝ s
    imageReconstructs :
      ∀ f → (Σ State (λ s → observe s ＝ f)) →
      observe (inverse f) ＝ f

open ExactReconstructionOnImage public

exactReconstructionOnImage-from-inverses :
  ∀ {State Feature : Set}
  {observe : State → Feature}
  {inverse : Feature → State} →
  (∀ s → inverse (observe s) ＝ s) →
  (∀ f → observe (inverse f) ＝ f) →
  ExactReconstructionOnImage State Feature observe inverse
exactReconstructionOnImage-from-inverses leftInverse rightInverse =
  exactReconstructionOnImage
    leftInverse
    (λ f _ → rightInverse f)

record GlobalConjugacyEquivalence
  (State Feature : Set)
  (step : State → State)
  (observe : State → Feature)
  (featureStep : Feature → Feature)
  (inverse : Feature → State) : Set₁ where
  constructor globalConjugacyEquivalence
  field
    forward :
      ∀ s → observe (step s) ＝ featureStep (observe s)
    stateReconstruction :
      ∀ s → inverse (observe s) ＝ s
    featureReconstruction :
      ∀ f → observe (inverse f) ＝ f
    stateDynamicsFromFeature :
      ∀ s → step s ＝ inverse (featureStep (observe s))
    featureDynamicsFromState :
      ∀ f → featureStep f ＝ observe (step (inverse f))

globalConjugacyEquivalence-iterate :
  ∀ {State Feature : Set}
    {step : State → State}
    {observe : State → Feature}
    {featureStep : Feature → Feature}
    {inverse : Feature → State}
    (G : GlobalConjugacyEquivalence
      State
      Feature
      step
      observe
      featureStep
      inverse)
    (n : ℕ)
    (s : State) →
  observe (iterateState step n s)
  ＝
  iterateState featureStep n (observe s)
globalConjugacyEquivalence-iterate G zero s = refl
globalConjugacyEquivalence-iterate {step = step} {featureStep = featureStep} G (succ n) s =
  trans
    (GlobalConjugacyEquivalence.forward G (iterateState step n s))
    (ap
      featureStep
      (globalConjugacyEquivalence-iterate G n s))

recurrentListState-append :
  ∀ {State Input : Set}
  (R : C.RecurrentNetwork State Input)
  (xs ys : List Input)
  (s : State) →
  C.recurrentListState R (xs ++ ys) s
  ＝
  C.recurrentListState R ys
    (C.recurrentListState R xs s)
recurrentListState-append R [] ys s = refl
recurrentListState-append R (x ∷ xs) ys s =
  recurrentListState-append
    R
    xs
    ys
    (C.runNetwork R s x)

canonicalTokenStep-conjugacy :
  ∀ (s : C.GRUState) (t : C.CanonicalToken) →
  C.runNetwork C.canonicalTokenRecurrentNetwork s t
  ＝
  C.runNetwork C.canonicalGRURecurrentNetwork
    s
    (C.canonicalTokenEncode t)
canonicalTokenStep-conjugacy s t = refl

canonicalTokenListState-conjugacy :
  ∀ (xs : C.CanonicalTokenSequence) (s : C.GRUState) →
  C.canonicalTokenListState xs s
  ＝
  C.recurrentListState
    C.canonicalGRURecurrentNetwork
    (C.canonicalTokenEncodeList xs)
    s
canonicalTokenListState-conjugacy [] s = refl
canonicalTokenListState-conjugacy (t ∷ ts) s =
  canonicalTokenListState-conjugacy
    ts
    (C.canonicalTokenStep s t)

canonicalToken-prefix-monoid-homomorphism :
  RecurrentPrefixMonoidHomomorphism
    C.GRUState
    C.CanonicalToken
canonicalToken-prefix-monoid-homomorphism =
  recurrentPrefixMonoidHomomorphism
    (λ R s → prefixListEndomorphism-unit R s)
    (λ R xs ys s → prefixListEndomorphism-append R xs ys s)

canonicalTokenLogitTrace-append :
  ∀ (K : C.CanonicalTokenLanguageModelKernel)
  (xs ys : C.CanonicalTokenSequence)
  (s : C.GRUState) →
  C.canonicalTokenLogitTrace K (xs ++ ys) s
  ＝
  C.canonicalTokenLogitTrace K xs s ++
  C.canonicalTokenLogitTrace K ys
    (C.canonicalTokenListState xs s)
canonicalTokenLogitTrace-append K [] ys s = refl
canonicalTokenLogitTrace-append K (t ∷ xs) ys s =
  ap
    (λ trace →
      C.logits K s ∷ trace)
    (canonicalTokenLogitTrace-append
      K
      xs
      ys
      (C.canonicalTokenStep s t))

record CanonicalGlobalTokenEncodingConjugacyTheorem : Set₁ where
  constructor canonicalGlobalTokenEncodingConjugacyTheorem
  field
    recurrentStepConjugacy :
      ∀ s t →
      C.runNetwork C.canonicalTokenRecurrentNetwork s t
      ＝
      C.runNetwork C.canonicalGRURecurrentNetwork
        s
        (C.canonicalTokenEncode t)
    recurrentListConjugacy :
      ∀ xs s →
      C.canonicalTokenListState xs s
      ＝
      C.recurrentListState
        C.canonicalGRURecurrentNetwork
        (C.canonicalTokenEncodeList xs)
        s

open CanonicalGlobalTokenEncodingConjugacyTheorem public

canonical-global-token-encoding-conjugacy :
  CanonicalGlobalTokenEncodingConjugacyTheorem
canonical-global-token-encoding-conjugacy =
  canonicalGlobalTokenEncodingConjugacyTheorem
    canonicalTokenStep-conjugacy
    canonicalTokenListState-conjugacy

record ExactFunctionIsomorphismTransportTheorem
  (S T A B : Set)
  (isoA : StateIsomorphism S A)
  (isoB : StateIsomorphism T B)
  (f : S → T) : Set₁ where
  constructor exactFunctionIsomorphismTransportTheorem
  field
    translatedFunction : A → B
    exactTransport :
      ∀ x →
      StateIsomorphism.to isoB (f x) ＝
      translatedFunction (StateIsomorphism.to isoA x)

exactFunctionIsomorphismTransport :
  ∀ {S T A B : Set}
    {isoA : StateIsomorphism S A}
    {isoB : StateIsomorphism T B}
    (f : S → T) →
  ExactFunctionIsomorphismTransportTheorem S T A B isoA isoB f
exactFunctionIsomorphismTransport {isoA = isoA} {isoB = isoB} f =
  exactFunctionIsomorphismTransportTheorem
    (λ a →
      StateIsomorphism.to isoB
        (f (StateIsomorphism.from isoA a)))
    (λ x →
      sym
        (ap
          (λ y → StateIsomorphism.to isoB (f y))
          (StateIsomorphism.from-to isoA x)))

record ExactRecurrentFunctionTranslationTheorem
  (S A : Set)
  (isoA : StateIsomorphism S A)
  (step : S → S)
  (stepA : A → A) : Set₁ where
  constructor exactRecurrentFunctionTranslationTheorem
  field
    recurrentConjugacy :
      ∀ x →
      StateIsomorphism.to isoA (step x) ＝
      stepA (StateIsomorphism.to isoA x)
    exactFunctionTransport :
      ∀ {T B : Set}
        {isoB : StateIsomorphism T B}
        (f : S → T) →
      ExactFunctionIsomorphismTransportTheorem
        S T A B isoA isoB f

exactRecurrentFunctionTranslation :
  ∀ {S A : Set}
    {isoA : StateIsomorphism S A}
    (step : S → S)
    (stepA : A → A)
    (conjugacy :
      ∀ x →
      StateIsomorphism.to isoA (step x) ＝
      stepA (StateIsomorphism.to isoA x)) →
  ExactRecurrentFunctionTranslationTheorem S A isoA step stepA
exactRecurrentFunctionTranslation step stepA conjugacy =
  exactRecurrentFunctionTranslationTheorem
    conjugacy
    (λ {T} {B} {isoB} f →
      exactFunctionIsomorphismTransport f)

-- Function representations compose without loss: transporting f and then g
-- agrees exactly with transporting their composition.  The witness below is
-- derived solely from the two commuting equalities; no extra representation
-- or convergence assumption is hidden in this interface.
record GeneralizedRepresentationTransportCompositionTheorem : Set₁ where
  constructor generalizedRepresentationTransportCompositionTheorem
  field
    exactFunctionTransport :
      ∀ {S T A B : Set}
        {isoA : StateIsomorphism S A}
        {isoB : StateIsomorphism T B}
        (f : S → T) →
      ExactFunctionIsomorphismTransportTheorem S T A B isoA isoB f
    functionCompositionTransport :
      ∀ {S T U A B D : Set}
        (isoS : StateIsomorphism S A)
        (isoT : StateIsomorphism T B)
        (isoU : StateIsomorphism U D)
        (f : S → T)
        (g : T → U)
        (fA : A → B)
        (gB : B → D)
        (fCommutes :
          ∀ x →
          StateIsomorphism.to isoT (f x) ＝
          fA (StateIsomorphism.to isoS x))
        (gCommutes :
          ∀ y →
          StateIsomorphism.to isoU (g y) ＝
          gB (StateIsomorphism.to isoT y)) →
        ∀ x →
        StateIsomorphism.to isoU (g (f x)) ＝
        gB (fA (StateIsomorphism.to isoS x))

generalizedRepresentationTransportComposition :
  GeneralizedRepresentationTransportCompositionTheorem
generalizedRepresentationTransportComposition =
  generalizedRepresentationTransportCompositionTheorem
    exactFunctionIsomorphismTransport
    (λ isoS isoT isoU f g fA gB fCommutes gCommutes x →
      trans
        (gCommutes (f x))
        (ap gB (fCommutes x)))

record CanonicalExactRNNLMTheorem : Set₁ where
  constructor canonicalExactRNNLMTheorem
  field
    globalTokenConjugacy :
      CanonicalGlobalTokenEncodingConjugacyTheorem
    recurrentTrace :
      ∀ (K : C.CanonicalTokenLanguageModelKernel)
      (xs ys : C.CanonicalTokenSequence)
      (s : C.GRUState) →
      C.canonicalTokenLogitTrace K (xs ++ ys) s
      ＝
      C.canonicalTokenLogitTrace K xs s ++
      C.canonicalTokenLogitTrace K ys
        (C.canonicalTokenListState xs s)

open CanonicalExactRNNLMTheorem public

canonical-exact-rnn-lm-theorem : CanonicalExactRNNLMTheorem
canonical-exact-rnn-lm-theorem =
  canonicalExactRNNLMTheorem
    canonical-global-token-encoding-conjugacy
    canonicalTokenLogitTrace-append

record CanonicalGlobalTokenLMCompositionTheorem : Set₁ where
  constructor canonicalGlobalTokenLMCompositionTheorem
  field
    globalTokenConjugacy :
      CanonicalGlobalTokenEncodingConjugacyTheorem
    tokenPrefixMonoid :
      RecurrentPrefixMonoidHomomorphism
        C.GRUState
        C.CanonicalToken
    traceAppend :
      ∀ (K : C.CanonicalTokenLanguageModelKernel)
      (xs ys : C.CanonicalTokenSequence)
      (s : C.GRUState) →
      C.canonicalTokenLogitTrace K (xs ++ ys) s
      ＝
      C.canonicalTokenLogitTrace K xs s ++
      C.canonicalTokenLogitTrace K ys
        (C.canonicalTokenListState xs s)

open CanonicalGlobalTokenLMCompositionTheorem public

canonical-global-token-lm-composition-theorem :
  CanonicalGlobalTokenLMCompositionTheorem
canonical-global-token-lm-composition-theorem =
  canonicalGlobalTokenLMCompositionTheorem
    canonical-global-token-encoding-conjugacy
    canonicalToken-prefix-monoid-homomorphism
    canonicalTokenLogitTrace-append

record CanonicalTokenArbitraryLengthGenerationTheorem : Set₁ where
  constructor canonicalTokenArbitraryLengthGenerationTheorem
  field
    stateConjugacy :
      ∀ (xs : C.CanonicalTokenSequence) (s : C.GRUState) →
      C.canonicalTokenListState xs s
      ＝
      C.recurrentListState
        C.canonicalGRURecurrentNetwork
        (C.canonicalTokenEncodeList xs)
        s

    traceAppend :
      ∀ (K : C.CanonicalTokenLanguageModelKernel)
      (xs ys : C.CanonicalTokenSequence)
      (s : C.GRUState) →
      C.canonicalTokenLogitTrace K (xs ++ ys) s
      ＝
      C.canonicalTokenLogitTrace K xs s ++
      C.canonicalTokenLogitTrace K ys
        (C.canonicalTokenListState xs s)

    prefixMonoid :
      RecurrentPrefixMonoidHomomorphism
        C.GRUState
        C.CanonicalToken

canonical-token-arbitrary-length-generation-theorem :
  CanonicalTokenArbitraryLengthGenerationTheorem
canonical-token-arbitrary-length-generation-theorem =
  canonicalTokenArbitraryLengthGenerationTheorem
    canonicalTokenListState-conjugacy
    canonicalTokenLogitTrace-append
    canonicalToken-prefix-monoid-homomorphism

canonicalIntegerHaarCross :
  C.intCodeAdd C.oneIntCode (C.intCodeNeg C.oneIntCode) ＝ C.zeroIntCode
canonicalIntegerHaarCross = refl

canonicalIntegerHaarEnergy :
  C.intCodeAdd C.oneIntCode C.oneIntCode ＝ C.intCodeOfNat 2
canonicalIntegerHaarEnergy = refl

record CanonicalIntegerHaarScaledOrthogonalityTheorem : Set₁ where
  constructor canonicalIntegerHaarScaledOrthogonalityTheorem
  field
    crossOrthogonality :
      C.intCodeAdd C.oneIntCode (C.intCodeNeg C.oneIntCode) ＝ C.zeroIntCode
    integerEnergy :
      C.intCodeAdd C.oneIntCode C.oneIntCode ＝ C.intCodeOfNat 2

open CanonicalIntegerHaarScaledOrthogonalityTheorem public

canonical-integer-haar-scaled-orthogonality-theorem :
  CanonicalIntegerHaarScaledOrthogonalityTheorem
canonical-integer-haar-scaled-orthogonality-theorem =
  canonicalIntegerHaarScaledOrthogonalityTheorem
    canonicalIntegerHaarCross
    canonicalIntegerHaarEnergy


------------------------------------------------------------------------
-- Full-composition theorem hub.
--
-- The graph connects the actual representation stack rather than
-- treating Haar features, recurrent composition, Watkins/F4 coupling,
-- and permutation obstruction as unrelated theorem islands.
------------------------------------------------------------------------

canonicalHaarAttentionRecurrent :
  C.HaarAccumulator →
  List C.IntCode →
  C.GRUState →
  C.GRUState
canonicalHaarAttentionRecurrent accumulator xs s =
  C.recurrentListState
    C.canonicalGRURecurrentNetwork
    (C.canonicalHaarFeaturedLinearScan accumulator xs)
    s

haarAccumulatorScan :
  C.HaarFeaturedLinearTransformer →
  C.HaarAccumulator →
  List C.IntCode →
  C.HaarAccumulator
haarAccumulatorScan T accumulator [] = accumulator
haarAccumulatorScan T accumulator (x ∷ xs) =
  haarAccumulatorScan
    T
    (C.haarAccumulatorStep T accumulator x)
    xs

haarLinearTransform-append :
  ∀ (T : C.HaarFeaturedLinearTransformer)
  (accumulator : C.HaarAccumulator)
  (xs ys : List C.IntCode) →
  C.haarLinearTransform T accumulator (xs ++ ys)
  ＝
  C.haarLinearTransform T accumulator xs ++
  C.haarLinearTransform
    T
    (haarAccumulatorScan T accumulator xs)
    ys
haarLinearTransform-append T accumulator [] ys =
  refl
haarLinearTransform-append T accumulator (x ∷ xs) ys =
  ap
    (λ tail →
      let
        nextAccumulator =
          C.haarAccumulatorStep T accumulator x
        output =
          C.haarQueryRead T nextAccumulator x
      in output ∷ tail)
    (haarLinearTransform-append
      T
      (C.haarAccumulatorStep T accumulator x)
      xs
      ys)

canonicalHaarAttentionRecurrent-append :
  ∀ (accumulator : C.HaarAccumulator)
  (xs ys : List C.IntCode)
  (s : C.GRUState) →
  canonicalHaarAttentionRecurrent
    accumulator
    (xs ++ ys)
    s
  ＝
  canonicalHaarAttentionRecurrent
    (haarAccumulatorScan
      C.canonicalHaarFeaturedTransformer
      accumulator
      xs)
    ys
    (canonicalHaarAttentionRecurrent accumulator xs s)
canonicalHaarAttentionRecurrent-append accumulator xs ys s =
  trans
    (ap
      (λ outputs →
        C.recurrentListState
          C.canonicalGRURecurrentNetwork
          outputs
          s)
      (haarLinearTransform-append
        C.canonicalHaarFeaturedTransformer
        accumulator
        xs
        ys))
    (recurrentListState-append
      C.canonicalGRURecurrentNetwork
      (C.canonicalHaarFeaturedLinearScan accumulator xs)
      (C.canonicalHaarFeaturedLinearScan
        (haarAccumulatorScan
          C.canonicalHaarFeaturedTransformer
          accumulator
          xs)
        ys)
      s)

canonicalHaarFeature-recurrent-step :
  ∀ (s : C.GRUState) (x : C.IntCode) →
  C.gruStep
    s
    (C.intCodeSub
      (pr₁ (C.canonicalCReLU8 x))
      (pr₂ (C.canonicalCReLU8 x)))
  ＝
  C.gruStep s x
canonicalHaarFeature-recurrent-step s x =
  ap
    (C.gruStep s)
    (C.canonicalHaarFeatureReconstruct x)

canonicalHaarFeature-recurrent-prefix :
  ∀ (xs : List C.IntCode) (s : C.GRUState) →
  C.recurrentListState
    C.canonicalGRURecurrentNetwork
    (map
      (λ x →
        C.intCodeSub
          (pr₁ (C.canonicalCReLU8 x))
          (pr₂ (C.canonicalCReLU8 x)))
      xs)
    s
  ＝
  C.recurrentListState
    C.canonicalGRURecurrentNetwork
    xs
    s
canonicalHaarFeature-recurrent-prefix [] s =
  refl
canonicalHaarFeature-recurrent-prefix (x ∷ xs) s =
  trans
    (canonicalHaarFeature-recurrent-prefix
      xs
      (C.gruStep
        s
        (C.intCodeSub
          (pr₁ (C.canonicalCReLU8 x))
          (pr₂ (C.canonicalCReLU8 x)))))
    (ap
      (C.recurrentListState
        C.canonicalGRURecurrentNetwork
        xs)
      (canonicalHaarFeature-recurrent-step s x))

record CanonicalHaarRecurrentCompositionTheorem : Set₁ where
  constructor canonicalHaarRecurrentCompositionTheorem
  field
    haarOrthogonality :
      CanonicalIntegerHaarScaledOrthogonalityTheorem
    cReLUInjective :
      ∀ {x y : C.IntCode} →
      C.canonicalCReLU8 x ＝
      C.canonicalCReLU8 y →
      x ＝ y
    attentionAppend :
      ∀ (accumulator : C.HaarAccumulator)
      (xs ys : List C.IntCode)
      (s : C.GRUState) →
      canonicalHaarAttentionRecurrent
        accumulator
        (xs ++ ys)
        s
      ＝
      canonicalHaarAttentionRecurrent
        (haarAccumulatorScan
          C.canonicalHaarFeaturedTransformer
          accumulator
          xs)
        ys
        (canonicalHaarAttentionRecurrent accumulator xs s)
    reconstructedStep :
      ∀ (s : C.GRUState) (x : C.IntCode) →
      C.gruStep
        s
        (intCodeSub
          (pr₁ (C.canonicalCReLU8 x))
          (pr₂ (C.canonicalCReLU8 x)))
      ＝
      C.gruStep s x
    reconstructedPrefix :
      ∀ (xs : List C.IntCode) (s : C.GRUState) →
      C.recurrentListState
        C.canonicalGRURecurrentNetwork
        (map
          (λ x →
            intCodeSub
              (pr₁ (C.canonicalCReLU8 x))
              (pr₂ (C.canonicalCReLU8 x)))
          xs)
        s
      ＝
      C.recurrentListState
        C.canonicalGRURecurrentNetwork
        xs
        s
    recurrentComposition :
      RecurrentPrefixMonoidHomomorphism
        C.GRUState
        C.IntCode

------------------------------------------------------------------------
-- Executable learner composition regression:
-- the Haar-featured linear transformer must feed the canonical recurrent
-- step through the same state transition, not remain theorem-only.
------------------------------------------------------------------------

canonicalFullStep-haar-rnn-composition :
  ∀ {A} (K : C.FullLearnerKernel A) (s : C.FullLearnerState A) →
  C.gru (C.canonicalFullStep K s) ＝
  C.gruStep
    (C.gru s)
    (C.haarQueryRead
      C.canonicalHaarFeaturedTransformer
      (C.haarAccumulatorStep
        C.canonicalHaarFeaturedTransformer
        (C.haarAccumulator s)
        (C.canonicalSignal K s))
      (C.canonicalSignal K s))
canonicalFullStep-haar-rnn-composition K s = refl

------------------------------------------------------------------------
-- KLA theorem/e-graph integration.
--
-- KLA's information-form Kalman layer has two algebraic scan branches:
--   1. the information mean is an affine recurrence;
--   2. the precision is a fractional-linear (Möbius) recurrence represented
--      by a 2×2 transition matrix.
--
-- The first branch is definitionally the existing canonical MonoidAffine.
-- The second is represented below at coefficient level; the actual Bayesian
-- precision recurrence remains a frontier because the canonical learner has
-- no precision field.
------------------------------------------------------------------------

data KLAAffineExpression : Set where
  klaMean : C.MonoidAffine → KLAAffineExpression
  canonicalMean : C.MonoidAffine → KLAAffineExpression

klaAffineInterpret :
  KLAAffineExpression → C.MonoidAffine
klaAffineInterpret (klaMean a) = a
klaAffineInterpret (canonicalMean a) = a

klaAffineRelated :
  KLAAffineExpression → KLAAffineExpression → Set
klaAffineRelated e f =
  klaAffineInterpret e ＝ klaAffineInterpret f

klaAffineRelated-refl :
  ∀ e → klaAffineRelated e e
klaAffineRelated-refl e = refl

klaAffineRelated-sym :
  ∀ {e f} → klaAffineRelated e f → klaAffineRelated f e
klaAffineRelated-sym = sym

klaAffineRelated-trans :
  ∀ {e f g} →
  klaAffineRelated e f →
  klaAffineRelated f g →
  klaAffineRelated e g
klaAffineRelated-trans = trans

klaAffineEGraphCongruence :
  EGraphCongruence KLAAffineExpression
klaAffineEGraphCongruence =
  eGraphCongruence
    klaAffineRelated
    klaAffineRelated-refl
    klaAffineRelated-sym
    klaAffineRelated-trans

klaAffineEGraphSemantics :
  EGraphSemanticInterpretation
    KLAAffineExpression
    C.MonoidAffine
klaAffineEGraphSemantics =
  eGraphSemanticInterpretation
    klaAffineEGraphCongruence
    klaAffineInterpret
    (λ eq → eq)

klaAffineAStarCostModel :
  AStarCostModel KLAAffineExpression
klaAffineAStarCostModel =
  aStarCostModel
    (λ _ _ → succ zero)
    (λ _ → zero)

klaAffineAStarClosure :
  AStarSemanticClosure
    KLAAffineExpression
    C.MonoidAffine
klaAffineAStarClosure =
  aStarSemanticClosure
    klaAffineEGraphSemantics
    klaAffineAStarCostModel

kla-affine-canonical-edge :
  ∀ a →
  CertifiedEGraphEdge
    klaAffineEGraphSemantics
    (klaMean a)
    (canonicalMean a)
kla-affine-canonical-edge a =
  certifiedEGraphEdge
    (semanticEdgeMetadata
      "KLA-information-mean"
      "canonical-MonoidAffine"
      "kla-mean-canonical-affine"
      []
      semanticProved
      kernelProof
      true)
    (path-step refl (path-refl (canonicalMean a)))

kla-affine-composition :
  ∀ f₁ b₁ f₂ b₂ →
  C._∘ₘ_
    (C.monoidAffine f₂ b₂)
    (C.monoidAffine f₁ b₁)
  ＝
  C.monoidAffine
    (C.intCodeMul f₂ f₁)
    (C.intCodeAdd (C.intCodeMul f₂ b₁) b₂)
kla-affine-composition f₁ b₁ f₂ b₂ = refl

------------------------------------------------------------------------
-- Möbius coefficient shape.  KLA represents each precision update by a
-- 2×2 transition matrix; the actual Bayesian recurrence remains a frontier
-- because this canonical state has no precision variable or field.
------------------------------------------------------------------------

record KLAMobiusMatrix : Set where
  constructor klaMobiusMatrix
  field
    m₁₁ m₁₂ m₂₁ m₂₂ : C.IntCode
open KLAMobiusMatrix public

klaMobiusTransition :
  C.IntCode → C.IntCode → C.IntCode → KLAMobiusMatrix
klaMobiusTransition p aSquared phi =
  klaMobiusMatrix
    (C.intCodeAdd C.oneIntCode (C.intCodeMul p phi))
    (C.intCodeMul aSquared phi)
    p
    aSquared

------------------------------------------------------------------------
-- Honest frontier theorem: affine information-mean equality does not carry
-- enough information to reconstruct an arbitrary KLA precision state.
------------------------------------------------------------------------

record KLAFullBeliefState : Set where
  constructor klaFullBeliefState
  field
    meanTransform : C.MonoidAffine
    precision : C.IntCode

klaAffineProjection :
  KLAFullBeliefState → C.MonoidAffine
klaAffineProjection s = KLAFullBeliefState.meanTransform s

klaAffineProjection-not-injective :
  ¬
  (∀ {s t : KLAFullBeliefState} →
    klaAffineProjection s ＝
    klaAffineProjection t →
    s ＝ t)
klaAffineProjection-not-injective derive =
  let
    a = C.monoidAffine C.oneIntCode C.zeroIntCode
    s = klaFullBeliefState a C.zeroIntCode
    t = klaFullBeliefState a C.oneIntCode
  in
  false-not-true
    (ap KLAFullBeliefState.precision
      (derive {s = s} {t = t} refl))

record KLAPrecisionBridgeWitness : Set₁ where
  constructor klaPrecisionBridgeWitness
  field
    precisionState : Set
    precisionProjection : precisionState → C.IntCode
    precisionStep : precisionState → precisionState
    mobiusStep : KLAMobiusMatrix → precisionState → precisionState
    correspondence :
      ∀ M s →
      precisionStep s ＝ mobiusStep M s

------------------------------------------------------------------------
-- No such precision witness is claimed for CanonicalFullLearnerState yet:
-- the state now contains the executable Haar accumulator, but still has no
-- Bayesian precision variable.  Therefore the affine KLA edge is proved,
-- while the precision edge is explicitly a frontier rather than a false
-- equivalence claim.
------------------------------------------------------------------------

kla-affine-canonical-path-sound :
  ∀ a →
  interpret klaAffineEGraphSemantics (klaMean a)
  ＝
  interpret klaAffineEGraphSemantics (canonicalMean a)
kla-affine-canonical-path-sound a =
  eGraph-certified-edge-sound (kla-affine-canonical-edge a)

-- Compose the executable Haar→GRU transition with the certified KLA affine e-graph edge; precision remains an explicit frontier.
record CanonicalHaarKLAAffineCompositionTheorem : Set₁ where
  constructor canonicalHaarKLAAffineCompositionTheorem
  field
    haarRNN :
      ∀ {A} (K : C.FullLearnerKernel A) (s : C.FullLearnerState A) →
      C.gru (C.canonicalFullStep K s) ＝
      C.gruStep
        (C.gru s)
        (C.canonicalHaarRecurrentInput K s)
    klaAffineScan :
      ∀ f₁ b₁ f₂ b₂ →
      C._∘ₘ_
        (C.monoidAffine f₂ b₂)
        (C.monoidAffine f₁ b₁)
      ＝
      C.monoidAffine
        (C.intCodeMul f₂ f₁)
        (C.intCodeAdd (C.intCodeMul f₂ b₁) b₂)
    klaCanonicalEdge :
      ∀ a →
      interpret klaAffineEGraphSemantics (klaMean a)
      ＝
      interpret klaAffineEGraphSemantics (canonicalMean a)

open CanonicalHaarKLAAffineCompositionTheorem public

canonical-haar-kla-affine-composition-theorem :
  CanonicalHaarKLAAffineCompositionTheorem
canonical-haar-kla-affine-composition-theorem =
  canonicalHaarKLAAffineCompositionTheorem
    canonicalFullStep-haar-rnn-composition
    kla-affine-composition
    kla-affine-canonical-path-sound

record CanonicalFullCompositionGraphTheorem : Set₁ where
  constructor canonicalFullCompositionGraphTheorem
  field
    haarRecurrent :
      CanonicalHaarRecurrentCompositionTheorem
    gruf4Watkins :
      CanonicalGRUF4WatkinsPrefixCompositionTheorem
    connectedLearner :
      CanonicalFullLearnerConnectedScanConjugacyTheorem
    permutationBoundary :
      CanonicalLearnerPermutationCompositionImpossibilityTheorem
    sparsemaxComposition :
      CanonicalPolymorphicSparsemaxCompositionTheorem
    haarExecutable :
      ∀ {A} (K : C.FullLearnerKernel A) (s : C.FullLearnerState A) →
      C.gru (C.canonicalFullStep K s) ＝
      C.gruStep
        (C.gru s)
        (C.canonicalHaarRecurrentInput K s)
    klaAffineEdge :
      ∀ a →
      CertifiedEGraphEdge
        klaAffineEGraphSemantics
        (klaMean a)
        (canonicalMean a)
    klaAffineCompositionLaw :
      ∀ f₁ b₁ f₂ b₂ →
      C._∘ₘ_
        (C.monoidAffine f₂ b₂)
        (C.monoidAffine f₁ b₁)
      ＝
      C.monoidAffine
        (C.intCodeMul f₂ f₁)
        (C.intCodeAdd (C.intCodeMul f₂ b₁) b₂)
    klaPrecisionFrontier :
      ¬
      (∀ {s t : KLAFullBeliefState} →
        klaAffineProjection s ＝
        klaAffineProjection t →
        s ＝ t)
    haarKlaAffineComposition :
      CanonicalHaarKLAAffineCompositionTheorem


canonical-haar-recurrent-composition-theorem :
  CanonicalHaarRecurrentCompositionTheorem
canonical-haar-recurrent-composition-theorem =
  canonicalHaarRecurrentCompositionTheorem
    canonical-integer-haar-scaled-orthogonality-theorem
    C.canonicalHaarFeatureInjective
    canonicalHaarAttentionRecurrent-append
    canonicalHaarFeature-recurrent-step
    canonicalHaarFeature-recurrent-prefix
    canonical-recurrent-prefix-monoid-homomorphism

canonical-full-composition-graph-theorem :
  CanonicalFullCompositionGraphTheorem
canonical-full-composition-graph-theorem =
  canonicalFullCompositionGraphTheorem
    canonical-haar-recurrent-composition-theorem
    canonical-gruf4-watkins-prefix-composition-theorem
    canonical-full-learner-connected-scan-conjugacy-theorem
    canonical-learner-permutation-composition-impossibility-theorem
    canonical-polymorphic-sparsemax-egraph-theorem
    canonicalFullStep-haar-rnn-composition
    kla-affine-canonical-edge
    kla-affine-composition
    klaAffineProjection-not-injective
     canonical-haar-kla-affine-composition-theorem

canonicalAStarZeroCost :
  (zero + zero) ＝ zero
canonicalAStarZeroCost = refl

canonicalAStarSuccessorCost :
  ∀ n → n + succ zero ＝ succ n
canonicalAStarSuccessorCost n = succ-right n zero

record CanonicalAStarCostGuidanceTheorem : Set₁ where
  constructor canonicalAStarCostGuidanceTheorem
  field
    zeroCostIdentity :
      (zero + zero) ＝ zero
    successorCostComposition :
      ∀ n → n + succ zero ＝ succ n
    exactTokenTrace :
      ∀ (K : C.CanonicalTokenLanguageModelKernel)
      (xs ys : C.CanonicalTokenSequence)
      (s : C.GRUState) →
      C.canonicalTokenLogitTrace K (xs ++ ys) s
      ＝
      C.canonicalTokenLogitTrace K xs s ++
      C.canonicalTokenLogitTrace K ys
        (C.canonicalTokenListState xs s)

open CanonicalAStarCostGuidanceTheorem public

canonical-a-star-cost-guidance-theorem :
  CanonicalAStarCostGuidanceTheorem
canonical-a-star-cost-guidance-theorem =
  canonicalAStarCostGuidanceTheorem
    canonicalAStarZeroCost
    canonicalAStarSuccessorCost
    canonicalTokenLogitTrace-append

record CanonicalEndogenousEGraphAStarTransportClosureTheorem : Set₁ where
  constructor canonicalEndogenousEGraphAStarTransportClosureTheorem
  field
    aStarGuidance :
      CanonicalAStarCostGuidanceTheorem
    representationTransport :
      GeneralizedRepresentationTransportCompositionTheorem
    endogenousTraceTransport :
      ∀ {S T A B : Set}
        {isoA : StateIsomorphism S A}
        {isoB : StateIsomorphism T B}
        (f : S → T) →
      ExactFunctionIsomorphismTransportTheorem S T A B isoA isoB f
    semanticEGraphAStarClosure :
      ∀ {Expression State : Set} →
      (A : AStarSemanticClosure Expression State) →
      ∀ {e f : Expression} →
      EGraphSemanticPath (semantics A) e f →
      interpret (semantics A) e ＝ interpret (semantics A) f

CanonicalEndogenousAStarTransportClosureTheorem :
  Set₁
CanonicalEndogenousAStarTransportClosureTheorem =
  CanonicalEndogenousEGraphAStarTransportClosureTheorem

open CanonicalEndogenousEGraphAStarTransportClosureTheorem public

record CanonicalFiniteCycleExclusionIsomorphismTheorem : Set₁ where
  constructor canonicalFiniteCycleExclusionIsomorphismTheorem
  field
    finiteCycleIterateConjugacy :
      ∀ {A B : Set}
        (iso : StateIsomorphism A B)
        (f : A → A)
        (g : B → B) →
        (∀ a → to iso (f a) ＝ g (to iso a)) →
        ∀ n a →
        to iso (iterateIsomorphism f n a)
        ＝
        iterateIsomorphism g n (to iso a)
    cycleTransport :
      ∀ {A B : Set}
        (iso : StateIsomorphism A B)
        (f : A → A)
        (g : B → B) →
        (∀ a → to iso (f a) ＝ g (to iso a)) →
        (∀ n a → iterateIsomorphism f (succ n) a ≢ a) →
        ∀ n a →
        iterateIsomorphism g (succ n) (to iso a) ≢ to iso a

open CanonicalFiniteCycleExclusionIsomorphismTheorem public

eGraphAStarIterate-isomorphism :
  ∀ {State : Set}
  (step : State → State) (n : ℕ) (s : State) →
  eGraphAStarIterate step n s ＝
  iterateIsomorphism step n s
eGraphAStarIterate-isomorphism step zero s = refl
eGraphAStarIterate-isomorphism step (succ n) s =
  eGraphAStarIterate-isomorphism
    step
    n
    (step s)


------------------------------------------------------------------------
-- Finite mixed-Nash graph convergence composition.
--
-- This is a constructive certificate theorem:
--   * finite-rank A* graph descent supplies eventual stability;
--   * a supplied stable->fixed law turns that stable node into a fixed
--     point of the finite game update;
--   * a supplied fixed->mixed-Nash law identifies that fixed point as
--     a mixed Nash profile;
--   * e-graph soundness separately supplies semantic endpoint equality;
--   * the existing finite-cycle isomorphism kernel transports convergence
--     across exact state conjugacies;
--   * the existing GRU tail kernel transports feature-tail stability to
--     eventual source-state stationarity.
--
-- The Brouwer reduction below gives the classical Nash existential
-- conclusion relative to an explicit analytical Brouwer witness. The
-- monolith does not hide a proof of Brouwer itself.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Brouwer -> Nash existence boundary.
--
-- Nash's finite-game existence theorem can be proved by Brouwer: construct
-- a continuous self-map of the finite mixed-strategy simplex whose fixed
-- points are exactly Nash equilibria.  The monolith keeps the analytic
-- fixed-point theorem explicit instead of silently treating a generic
-- e-graph fixed point as a Nash equilibrium.
------------------------------------------------------------------------

record BrouwerMixedNashExistence
  (Profile : Set)
  (mixedNash : Profile → Set) : Set₁ where
  constructor brouwerMixedNashExistence
  field
    simplex : Set
    inProfile : simplex ＝ Profile
    brouwerMap : Profile → Profile
    continuous : Set
    fixedPoint :
      Σ Profile (λ p → brouwerMap p ＝ p)
    fixedImpliesNash :
      ∀ p →
      brouwerMap p ＝ p →
      mixedNash p

open BrouwerMixedNashExistence public

-- Every finite game is represented here by its finite mixed-strategy
-- simplex plus the continuous Brouwer map used in Nash's construction.
-- The result is existential: at least one mixed Nash profile exists.
nashEveryFiniteGameViaBrouwer :
  ∀ {Profile : Set}
  (mixedNash : Profile → Set)
  (N : BrouwerMixedNashExistence
    Profile
    mixedNash) →
  Σ Profile (λ p → mixedNash p)
nashEveryFiniteGameViaBrouwer mixedNash N
  with fixedPoint N
... | p , fixed =
  p , fixedImpliesNash N p fixed

record StationaryLimitTheorem
  (Distribution : Set)
  (P : Distribution → Distribution)
  (μ : ℕ → Distribution)
  (μ∞ : Distribution)
  (Converges : (ℕ → Distribution) → Distribution → Set) : Set₁ where
  constructor stationaryLimitTheorem
  field
    transitionLaw :
      ∀ n → μ (succ n) ＝ P (μ n)
    converges :
      Converges μ μ∞
    limitPreserved :
      Converges μ μ∞ → P μ∞ ＝ μ∞

record FiniteMixedNashBrouwerGRUEGraphAStarDistributionTheorem
  (Expression Profile State Distribution : Set)
  (mixedNash : Profile → Set)
  (stateStep : State → State)
  (featureStep : Profile → Profile)
  (encode : State → Profile)
  (P : Distribution → Distribution)
  (μ : ℕ → Distribution)
  (μ∞ : Distribution)
  (Converges : (ℕ → Distribution) → Distribution → Set) : Set₁ where
  constructor finiteMixedNashBrouwerGRUEGraphAStarDistributionTheorem
  field
    brouwerNash :
      BrouwerMixedNashExistence
        Profile
        mixedNash
    eGraphWitness :
      EGraphAStarFiniteRankConvergenceWitness
        Expression
        Profile
    gruWitness :
      GRUInjectiveTailStabilityConvergenceIdentifiabilityTheorem
        State
        Profile
        stateStep
        featureStep
        encode
    brouwerMapAgrees :
      ∀ p →
      brouwerMap brouwerNash p ＝
      step eGraphWitness p
    stableImpliesFixed :
      ∀ s →
      stable eGraphWitness s →
      step eGraphWitness s ＝ s
    featureFixedImpliesMixedNash :
      ∀ f →
      featureStep f ＝ f →
      mixedNash f
    distributionWitness :
      StationaryLimitTheorem
        Distribution
        P
        μ
        μ∞
        Converges

open FiniteMixedNashBrouwerGRUEGraphAStarDistributionTheorem public

finiteMixedNash-brouwer-gru-egraph-astar-distribution-proof :
  ∀ {Expression Profile State Distribution : Set}
  {mixedNash : Profile → Set}
  {stateStep : State → State}
  {featureStep : Profile → Profile}
  {encode : State → Profile}
  {P : Distribution → Distribution}
  {μ : ℕ → Distribution}
  {μ∞ : Distribution}
  {Converges : (ℕ → Distribution) → Distribution → Set}
  (N :
    BrouwerMixedNashExistence
      Profile
      mixedNash)
  (W :
    EGraphAStarFiniteRankConvergenceWitness
      Expression
      Profile)
  (G :
    GRUInjectiveTailStabilityConvergenceIdentifiabilityTheorem
      State
      Profile
      stateStep
      featureStep
      encode)
  (brouwerMapAgrees :
    ∀ p →
    brouwerMap N p ＝
    step W p)
  (stableImpliesFixed :
    ∀ s →
    stable W s →
    step W s ＝ s)
  (featureFixedImpliesMixedNash :
    ∀ f →
    featureStep f ＝ f →
    mixedNash f)
  (D :
    StationaryLimitTheorem
      Distribution
      P
      μ
      μ∞
      Converges) →
  FiniteMixedNashBrouwerGRUEGraphAStarDistributionTheorem
    Expression
    Profile
    State
    Distribution
    mixedNash
    stateStep
    featureStep
    encode
    P
    μ
    μ∞
    Converges
finiteMixedNash-brouwer-gru-egraph-astar-distribution-proof
  N W G
  brouwerMapAgrees
  stableImpliesFixed
  featureFixedImpliesMixedNash
  D =
  finiteMixedNashBrouwerGRUEGraphAStarDistributionTheorem
    N
    W
    G
    brouwerMapAgrees
    stableImpliesFixed
    featureFixedImpliesMixedNash
    D

finiteMixedNash-brouwer-gru-egraph-astar-distribution-proof-nash :
  ∀ {Expression Profile State Distribution : Set}
  {mixedNash : Profile → Set}
  {stateStep : State → State}
  {featureStep : Profile → Profile}
  {encode : State → Profile}
  {P : Distribution → Distribution}
  {μ : ℕ → Distribution}
  {μ∞ : Distribution}
  {Converges : (ℕ → Distribution) → Distribution → Set}
  (W :
    FiniteMixedNashBrouwerGRUEGraphAStarDistributionTheorem
      Expression
      Profile
      State
      Distribution
      mixedNash
      stateStep
      featureStep
      encode
      P
      μ
      μ∞
      Converges) →
  Σ Profile
    (λ p →
      mixedNash p)
finiteMixedNash-brouwer-gru-egraph-astar-distribution-proof-nash
  {mixedNash = mixedNash} W =
  nashEveryFiniteGameViaBrouwer
    mixedNash
    (brouwerNash W)

finiteMixedNash-brouwer-gru-egraph-astar-distribution-fixed :
  ∀ {Expression Profile State Distribution : Set}
  {mixedNash : Profile → Set}
  {stateStep : State → State}
  {featureStep : Profile → Profile}
  {encode : State → Profile}
  {P : Distribution → Distribution}
  {μ : ℕ → Distribution}
  {μ∞ : Distribution}
  {Converges : (ℕ → Distribution) → Distribution → Set}
  (W :
    FiniteMixedNashBrouwerGRUEGraphAStarDistributionTheorem
      Expression
      Profile
      State
      Distribution
      mixedNash
      stateStep
      featureStep
      encode
      P
      μ
      μ∞
      Converges) →
  P μ∞ ＝ μ∞
finiteMixedNash-brouwer-gru-egraph-astar-distribution-fixed W =
  StationaryLimitTheorem.limitPreserved
    (distributionWitness W)
    (StationaryLimitTheorem.converges (distributionWitness W))

record MixedNashFixedPointBridge
  (Profile : Set)
  (update : Profile → Profile) : Set₁ where
  constructor mixedNashFixedPointBridge
  field
    mixedNash : Profile → Set
    fixedImpliesMixedNash :
      ∀ p →
      update p ＝ p →
      mixedNash p

open MixedNashFixedPointBridge public

brouwerMixedNashFixedPointBridge :
  ∀ {Profile : Set}
  {update : Profile → Profile}
  {mixedNash : Profile → Set}
  (N :
    BrouwerMixedNashExistence
      Profile
      mixedNash)
  (brouwerMapAgrees :
    ∀ p →
    brouwerMap N p ＝
    update p) →
  MixedNashFixedPointBridge
    Profile
    update
brouwerMixedNashFixedPointBridge
  N
  brouwerMapAgrees =
  mixedNashFixedPointBridge
    (mixedNash N)
    (λ p fixed →
      fixedImpliesNash
        N
        p
        (trans
          (brouwerMapAgrees p)
          fixed))


-- The Brouwer bridge above is the analytical Nash-existence seam:
-- Brouwer supplies a fixed point of Nash's continuous self-map, while the
-- A* / e-graph theorem supplies finite-rank convergence to a stable update.
-- When the maps agree, the two certificates compose without treating A*
-- cost as proof evidence.
finiteMixedNash-brouwer-egraph-astar-proof :
  ∀ {Expression Profile : Set}
  {mixedNash : Profile → Set}
  (N :
    BrouwerMixedNashExistence
      Profile
      mixedNash)
  (W :
    EGraphAStarFiniteRankConvergenceWitness
      Expression
      Profile)
  (brouwerMapAgrees :
    ∀ p →
    brouwerMap N p ＝
    step W p)
  (stableImpliesFixed :
    ∀ s →
    stable W s →
    step W s ＝ s) →
  ∀ s →
  ((Σ ℕ
    (λ n →
      mixedNash
        (eGraphAStarIterate
          (step W)
          n
          s)))
   ×
   (Σ ℕ
    (λ n →
      interpret
        (semantics (closure W))
        (candidate W
          (eGraphAStarIterate
            (step W)
            n
            s))
      ＝
      interpret
        (semantics (closure W))
        (target W)))
   ×
   (Σ Profile (λ p → mixedNash p)))
finiteMixedNash-brouwer-egraph-astar-proof
  N
  W
  brouwerMapAgrees
  stableImpliesFixed
  s
  with eventualStable W s
... | n , stableAtN =
  ( ( n
    , fixedImpliesMixedNash
        (brouwerMixedNashFixedPointBridge
          N
          brouwerMapAgrees)
        (eGraphAStarIterate
          (step W)
          n
          s)
        (stableImpliesFixed
          (eGraphAStarIterate
            (step W)
            n
            s)
          stableAtN))
  , eGraphAStarConvergenceSemanticClosure W s )
  , nashEveryFiniteGameViaBrouwer
      (mixedNash N)
      N


finiteMixedNash-egraph-astar-convergence :
  ∀ {Expression Profile : Set}
  (W :
    EGraphAStarFiniteRankConvergenceWitness
      Expression
      Profile)
  (B :
    MixedNashFixedPointBridge
      Profile
      (step W))
  (stableImpliesFixed :
    ∀ s →
    stable W s →
    step W s ＝ s) →
  ∀ s →
  Σ ℕ
    (λ n →
      mixedNash B
        (eGraphAStarIterate
          (step W)
          n
          s))
finiteMixedNash-egraph-astar-convergence W B stableImpliesFixed s
  with eventualStable W s
... | n , stableAtN =
  n ,
  fixedImpliesMixedNash B
    (eGraphAStarIterate
      (step W)
      n
      s)
    (stableImpliesFixed
      (eGraphAStarIterate
        (step W)
        n
        s)
      stableAtN)

finiteMixedNash-egraph-astar-eventualStationarity :
  ∀ {Expression Profile : Set}
  (W :
    EGraphAStarFiniteRankConvergenceWitness
      Expression
      Profile)
  (B :
    MixedNashFixedPointBridge
      Profile
      (step W))
  (stableImpliesFixed :
    ∀ s →
    stable W s →
    step W s ＝ s) →
  ∀ s →
  Σ ℕ
    (λ n →
      ∀ k →
      eGraphAStarIterate
        (step W)
        (n + k)
        s
      ＝
      eGraphAStarIterate
        (step W)
        n
        s)
finiteMixedNash-egraph-astar-eventualStationarity
  W B stableImpliesFixed s
  with eventualStable W s
... | n , stableAtN =
  n ,
  λ k →
    trans
      (iterateStep-add
        (step W)
        n
        k
        s)
      (iterateStep-fixed
        (step W)
        (stableImpliesFixed
          (eGraphAStarIterate
            (step W)
            n
            s)
          stableAtN)
        k)

finiteMixedNash-egraph-astar-proof :
  ∀ {Expression Profile : Set}
  (W :
    EGraphAStarFiniteRankConvergenceWitness
      Expression
      Profile)
  (B :
    MixedNashFixedPointBridge
      Profile
      (step W))
  (stableImpliesFixed :
    ∀ s →
    stable W s →
    step W s ＝ s) →
  ∀ s →
  (Σ ℕ
    (λ n →
      mixedNash B
        (eGraphAStarIterate
          (step W)
          n
          s)))
  ×
  (Σ ℕ
    (λ n →
      interpret
        (semantics (closure W))
        (candidate W
          (eGraphAStarIterate
            (step W)
            n
            s))
      ＝
      interpret
        (semantics (closure W))
        (target W)))
finiteMixedNash-egraph-astar-proof W B stableImpliesFixed s =
  finiteMixedNash-egraph-astar-convergence
    W B stableImpliesFixed s
  ,
  eGraphAStarConvergenceSemanticClosure W s

finiteMixedNash-cycle-transport :
  ∀ {Expression ProfileA ProfileB : Set}
  (W :
    EGraphAStarFiniteRankConvergenceWitness
      Expression
      ProfileA)
  (B :
    MixedNashFixedPointBridge
      ProfileA
      (step W))
  (stableImpliesFixed :
    ∀ s →
    stable W s →
    step W s ＝ s)
  (cycleTransport :
    CanonicalFiniteCycleExclusionIsomorphismTheorem)
  (iso :
    StateIsomorphism
      ProfileA
      ProfileB)
  (stepB : ProfileB → ProfileB)
  (conjugacy :
    ∀ p →
    to iso (step W p) ＝
    stepB (to iso p))
  (sourceNoFiniteCycle :
    ∀ n p →
    iterateIsomorphism
      (step W)
      (succ n)
      p
      ≢
      p)
  (mixedNashB :
    ProfileB → Set)
  (transportNash :
    ∀ p →
    mixedNash B p →
    mixedNashB (to iso p)) →
  ∀ s →
  (Σ ℕ
    (λ n →
      mixedNashB
        (eGraphAStarIterate
          stepB
          n
          (to iso s))))
  ×
  (∀ n p →
    iterateIsomorphism
      stepB
      (succ n)
      (to iso p)
      ≢
      to iso p)
finiteMixedNash-cycle-transport
  W
  B
  stableImpliesFixed
  cycleTransport
  iso
  stepB
  conjugacy
  sourceNoFiniteCycle
  mixedNashB
  transportNash
  s
  with finiteMixedNash-egraph-astar-convergence
    W B stableImpliesFixed s
... | n , nashAtN =
  ( n
    ,
    transport (λ p → mixedNashB p)
      targetIterateEquality
      (transportNash
        (eGraphAStarIterate
          (step W)
          n
          s)
        nashAtN)
  )
  ,
  cycleTransport . cycleTransport
    iso
    (step W)
    stepB
    conjugacy
    sourceNoFiniteCycle
  where
  sourceTargetIterateEquality :
    ∀ k →
    to iso
      (iterateIsomorphism
        (step W)
        k
        s)
    ＝
    iterateIsomorphism
      stepB
      k
      (to iso s)
  sourceTargetIterateEquality k =
    stepConjugacy-iterate
      (stepConjugacyWitness
        iso
        conjugacy)
      k
      s

  targetIterateEquality :
    to iso
      (eGraphAStarIterate
        (step W)
        n
        s)
    ＝
    eGraphAStarIterate
      stepB
      n
      (to iso s)
  targetIterateEquality =
    trans
      (ap
        (to iso)
        (eGraphAStarIterate-isomorphism
          (step W)
          n
          s))
      (trans
        (sourceTargetIterateEquality n)
        (sym
          (eGraphAStarIterate-isomorphism
            stepB
            n
            (to iso s))))

finiteMixedNash-from-GRU-tail :
  ∀ {State Feature : Set}
  {stateStep : State → State}
  {featureStep : Feature → Feature}
  {encode : State → Feature}
  (W :
    GRUInjectiveTailStabilityConvergenceIdentifiabilityTheorem
      State
      Feature
      stateStep
      featureStep
      encode)
  (mixedNash : Feature → Set)
  (featureFixedImpliesMixedNash :
    ∀ f →
    featureStep f ＝ f →
    mixedNash f) →
  ∀ s →
  Σ ℕ
    (λ n →
      mixedNash
        (encode
          (iterateStep
            stateStep
            n
            s)))
finiteMixedNash-from-GRU-tail
  {State}
  {Feature}
  {stateStep}
  {featureStep}
  {encode}
  W
  mixedNash
  featureFixedImpliesMixedNash
  s
  with gruInjectiveTailStability-tailFixedPoint W s
... | n , fixed =
  n ,
  featureFixedImpliesMixedNash
    (encode
      (iterateStep
        stateStep
        n
        s))
    (trans
      (sym
        (stepConjugacy W
          (iterateStep
            stateStep
            n
            s)))
      (ap
        encode
        fixed))


record CanonicalOperatorCompositionTheorem : Set₁ where
  constructor canonicalOperatorCompositionTheorem
  field
    identity :
      ∀ {S : Set} (s : S) →
      C.applyEndomorphism
        (C.identityEndomorphism {State = S}) s
      ＝ s
    composition :
      ∀ {S : Set}
        (f g : C.Endomorphism S) (s : S) →
      C.applyEndomorphism
        (C.composeEndomorphism f g) s
      ＝
      C.applyEndomorphism f
        (C.applyEndomorphism g s)
    associativity :
      ∀ {S : Set}
        (f g h : C.Endomorphism S) (s : S) →
      C.applyEndomorphism
        (C.composeEndomorphism
          (C.composeEndomorphism f g) h) s
      ＝
      C.applyEndomorphism
        (C.composeEndomorphism
          f (C.composeEndomorphism g h)) s

open CanonicalOperatorCompositionTheorem public

canonical-operator-composition-theorem :
  CanonicalOperatorCompositionTheorem
canonical-operator-composition-theorem =
  canonicalOperatorCompositionTheorem
    (λ s → refl)
    (λ f g s → refl)
    C.endomorphismAssociative

f4Orbit :
  C.F4IntUKernel → C.IntCode → ℕ → C.F4IntUState → C.F4IntUState
f4Orbit K g zero s = s
f4Orbit K g (succ n) s =
  C.f4ThetaStep K (f4Orbit K g n s) g

record F4UpperBoundedTrajectory
  (K : C.F4IntUKernel)
  (g : C.IntCode)
  (s : C.F4IntUState) : Set₁ where
  constructor f4UpperBoundedTrajectory
  field
    bound : ℕ
    bounded :
      ∀ n →
      C.intCodeValue (C.thetaQ (f4Orbit K g n s)) ≤ pos bound

nat-plus-one :
  ∀ n → n + succ zero ＝ succ n
nat-plus-one n =
  trans
    (succ-right n zero)
    (ap succ (zero-right-neutral n))

integer-nat-plus-one :
  ∀ n → (pos n) +Int (pos 1) ＝ pos (succ n)
integer-nat-plus-one n =
  ap pos (nat-plus-one n)

f4-zero-L2-unit-step-code :
  ∀ s →
  C.intCodeValue
    (C.thetaQ
      (C.f4ThetaStep
        (C.f4IntUKernel C.zeroIntCode)
        s
        C.oneIntCode))
  ＝
  C.intCodeValue (C.thetaQ s) +Int (pos 1)
f4-zero-L2-unit-step-code s =
  trans
    (ap C.intCodeValue
      (C.f4ParameterInvariant
        (C.f4IntUKernel C.zeroIntCode)
        s
        C.oneIntCode))
    (ℤ-zero-right-neutral
      (C.intCodeValue (C.thetaQ s) +Int (pos 1)))

f4-unit-forcing-linear-growth :
  ∀ n s →
  C.intCodeValue
    (C.thetaQ
      (f4Orbit
        (C.f4IntUKernel C.zeroIntCode)
        C.oneIntCode
        n
        s))
  ＝
  C.intCodeValue (C.thetaQ s) +Int (pos n)
f4-unit-forcing-linear-growth zero s =
  sym (ℤ-zero-right-neutral (C.intCodeValue (C.thetaQ s)))
f4-unit-forcing-linear-growth (succ n) s =
  trans
    (f4-zero-L2-unit-step-code
      (f4Orbit (C.f4IntUKernel C.zeroIntCode) C.oneIntCode n s))
    (trans
      (ap
        (λ z → z +Int (pos 1))
        (f4-unit-forcing-linear-growth n s))
      (trans
        (ℤ+-assoc
          (C.intCodeValue (C.thetaQ s))
          (pos n)
          (pos 1))
        (ap
          (λ z → C.intCodeValue (C.thetaQ s) +Int z)
          (integer-nat-plus-one n))))

nat-succ-not-le :
  ∀ n → succ n ≤ n → ⊥
nat-succ-not-le zero ()
nat-succ-not-le (succ n) h =
  nat-succ-not-le n h

f4-unit-forcing-no-upper-bound :
  ∀ {s : C.F4IntUState} →
  C.thetaQ s ＝ C.zeroIntCode →
  ¬ F4UpperBoundedTrajectory
      (C.f4IntUKernel C.zeroIntCode)
      C.oneIntCode
      s
f4-unit-forcing-no-upper-bound thetaZero boundedWitness =
  let
    B = F4UpperBoundedTrajectory.bound boundedWitness
    horizonBound = F4UpperBoundedTrajectory.bounded boundedWitness (succ B)
    growth =
      f4-unit-forcing-linear-growth
        (succ B)
        _
    growthFromZero :
      C.intCodeValue
        (C.thetaQ
          (f4Orbit
            (C.f4IntUKernel C.zeroIntCode)
            C.oneIntCode
            (succ B)
            _))
      ＝
      pos (succ B)
    growthFromZero =
      trans
        growth
        (trans
          (ap
            (λ z → z +Int (pos (succ B)))
            (ap C.intCodeValue thetaZero))
          (ℤ-zero-left-neutral (pos (succ B))))
    impossibleOrder :
      pos (succ B) ≤ pos B
    impossibleOrder =
      transport (λ z → z ≤ pos B)
        growthFromZero
        horizonBound
  in
    nat-succ-not-le B
      (ℤ-bigger-or-equal-not-less (pos (succ B)) (pos B) impossibleOrder
       (ℕ-order-respects-ℤ-order B (succ B) (<-succ B)))

record CanonicalPureNonOrangeBypassCompletionTheorem : Set₁ where
  constructor canonicalPureNonOrangeBypassCompletionTheorem
  field
    recurrentPrefix :
      RecurrentPrefixMonoidHomomorphism C.GRUState C.IntCode
    fullLearnerScanConjugacy :
      CanonicalFullLearnerConnectedScanConjugacyTheorem
    exactTuringBoundary :
      ¬ CanonicalExactCompositionTuringCompletenessContract
    finiteCycleIsomorphismTransport :
      CanonicalFiniteCycleExclusionIsomorphismTheorem
    operatorComposition :
      CanonicalOperatorCompositionTheorem
    f4OptimizerStability :
      CanonicalF4GlobalOptimizerStabilityTheorem
    integerHaarOrthogonality :
      CanonicalIntegerHaarScaledOrthogonalityTheorem

open CanonicalPureNonOrangeBypassCompletionTheorem public

-- Persistent excitation remains a conditional learner obligation.
-- No unconditional theorem is registered here without a stated predicate
-- and a proof derived from the canonical learner semantics.

record ExactContractComputabilityBoundaryTheorem : Set₁ where
  constructor exactContractComputabilityBoundaryTheorem
  field
    specifiedContractImpossible :
      ¬ CanonicalExactCompositionTuringCompletenessContract
    scopeIsContractSpecific :
      ⊤

exact-contract-computability-boundary-theorem :
  ExactContractComputabilityBoundaryTheorem
exact-contract-computability-boundary-theorem =
  exactContractComputabilityBoundaryTheorem
    canonicalExactCompositionTuringCompletenessContract-impossible
    tt

record CanonicalStationarySubcompositionTheorem : Set₁ where
  constructor canonicalStationarySubcompositionTheorem
  field
    stationaryLimitContract :
      ∀ {Distribution : Set}
        (P : Distribution → Distribution)
        (μ : ℕ → Distribution)
        (π : Distribution)
        (Converges : (ℕ → Distribution) → Distribution → Set) →
      (∀ n → μ (succ n) ＝ P (μ n)) →
      Converges μ π →
      (Converges μ π → P π ＝ π) →
      StationaryLimitTheorem
        Distribution P μ π Converges

canonical-stationary-subcomposition-theorem :
  CanonicalStationarySubcompositionTheorem
canonical-stationary-subcomposition-theorem =
  canonicalStationarySubcompositionTheorem
    (λ P μ π Converges transitionLaw convergence limitPreserved →
      stationaryLimitTheorem
        transitionLaw
        convergence
        limitPreserved)

record DistributionalStationaryAggregateTransport
  (Distribution Economic : Set)
  (P : Distribution → Distribution)
  (μ : ℕ → Distribution)
  (μ∞ : Distribution)
  (Converges : (ℕ → Distribution) → Distribution → Set)
  (aggregate : Distribution → Economic)
  (economicStep : Economic → Economic) : Set₁ where
  constructor distributionalStationaryAggregateTransport
  field
    stationaryLimit :
      StationaryLimitTheorem
        Distribution
        P
        μ
        μ∞
        Converges
    aggregateStepCommutes :
      ∀ d →
      aggregate (P d) ＝
      economicStep (aggregate d)

open DistributionalStationaryAggregateTransport public

distributionalStationaryAggregate-stationary :
  ∀ {Distribution Economic : Set}
  {P : Distribution → Distribution}
  {μ : ℕ → Distribution}
  {μ∞ : Distribution}
  {Converges : (ℕ → Distribution) → Distribution → Set}
  {aggregate : Distribution → Economic}
  {economicStep : Economic → Economic}
  (W :
    DistributionalStationaryAggregateTransport
      Distribution
      Economic
      P
      μ
      μ∞
      Converges
      aggregate
      economicStep) →
  economicStep (aggregate μ∞) ＝ aggregate μ∞
distributionalStationaryAggregate-stationary W =
  trans
    (sym (aggregateStepCommutes W _))
    (ap
      aggregate
      (StationaryLimitTheorem.limitPreserved
        (stationaryLimit W)
        (StationaryLimitTheorem.converges (stationaryLimit W))))

record FunctionClassInclusion
  (Input Output : Set)
  (FBase FFull : (Input → Output) → Set₁) : Set₁ where
  constructor functionClassInclusion
  field
    include :
      ∀ {f : Input → Output} →
      FBase f →
      FFull f

record StrictFunctionClassSeparation
  (Input Output : Set)
  (FBase FFull : (Input → Output) → Set₁) : Set₁ where
  constructor strictFunctionClassSeparation
  field
    inclusion :
      FunctionClassInclusion Input Output FBase FFull
    witness :
      Input → Output
    witnessInFull :
      FFull witness
    witnessNotInBase :
      ¬ FBase witness

twoPow : ℕ → ℕ
twoPow zero = succ zero
twoPow (succ k) = twoPow k + twoPow k

nat-plus-right-mono :
  ∀ {a b c : ℕ} → a ≤ b → a + c ≤ b + c
nat-plus-right-mono {a} {b} {c} p = helper a b p c
 where
  P : (m n : ℕ) → m ≤ n → Set
  P m n _ = (k : ℕ) → m + k ≤ n + k

  base : (n : ℕ) → P zero n (zero-least n)
  base n k =
    transport
      (λ x → x ≤ n + k)
      (zero-left-neutral k ⁻¹)
      (≤-+' n k)

  nat-plus-right-mono-succ :
    (m n : ℕ) (q : m ≤ n) →
    P m n q →
    P (succ m) (succ n) (succ-monotone m n q)
  nat-plus-right-mono-succ m n q ih k =
    transport
      (λ y → succ m + k ≤ y)
      (succ-left n k ⁻¹)
      (transport
        (λ x → x ≤ succ (n + k))
        (succ-left m k ⁻¹)
        (succ-monotone (m + k) (n + k) (ih k)))

  helper : (m n : ℕ) (q : m ≤ n) → P m n q
  helper = ≤-induction P base nat-plus-right-mono-succ

record EfficientOperatorMonoidRepresentation
  (State Input : Set) : Set₁ where
  constructor efficientOperatorMonoidRepresentation
  field
    operator :
      Input → C.Endomorphism State
    operatorAssociative :
      ∀ (f g h : C.Endomorphism State) s →
      C.applyEndomorphism
        (C.composeEndomorphism
          (C.composeEndomorphism f g)
          h)
        s
      ＝
      C.applyEndomorphism
        (C.composeEndomorphism
          f
          (C.composeEndomorphism g h))
        s
    representationSpan : ℕ
    decodingSpan : ℕ
    compositionSpan : ℕ
    compositionWork : ℕ
    scanSpan : ℕ → ℕ
    scanWork : ℕ → ℕ
    scanSpan-linear :
      ∀ h →
      scanSpan h ≤ compositionSpan + compositionSpan * h
    scanWork-linear :
      ∀ h →
      scanWork h ≤ compositionWork * h

record ParallelPrefixComplexityCertificate
  (State Input : Set) : Set₁ where
  constructor parallelPrefixComplexityCertificate
  field
    monoidRepresentation :
      EfficientOperatorMonoidRepresentation State Input
    exactScan :
      RecurrentAssociativeScanTheorem State Input
    totalSpan :
      ℕ → ℕ
    totalWork :
      ℕ → ℕ
    totalSpan-definition :
      ∀ h →
      totalSpan h ＝
        EfficientOperatorMonoidRepresentation.representationSpan
          monoidRepresentation
        + EfficientOperatorMonoidRepresentation.scanSpan
            monoidRepresentation h
        + EfficientOperatorMonoidRepresentation.decodingSpan
            monoidRepresentation
    totalWork-definition :
      ∀ h →
      totalWork h ＝
        EfficientOperatorMonoidRepresentation.scanWork
          monoidRepresentation h

record LogarithmicScanSpanCertificate
  (State Input : Set) : Set₁ where
  constructor logarithmicScanSpanCertificate
  field
    scanSpan : ℕ → ℕ
    coefficient : ℕ
    additive : ℕ
    scanSpan-bound :
      ∀ k h →
      h ≤ twoPow k →
      scanSpan h ≤ coefficient * k + additive

record LogarithmicPrefixScanComplexityTheorem
  (State Input : Set) : Set₁ where
  constructor logarithmicPrefixScanComplexityTheorem
  field
    exactScan :
      RecurrentAssociativeScanTheorem State Input
    operatorMonoid :
      EfficientOperatorMonoidRepresentation State Input
    logarithmicSpan :
      LogarithmicScanSpanCertificate State Input
    representationOverhead :
      ℕ
    decodingOverhead :
      ℕ
    horizonSpan :
      ℕ → ℕ
    horizonWork :
      ℕ → ℕ
    horizonSpan-definition :
      ∀ h →
      horizonSpan h ＝
        LogarithmicScanSpanCertificate.scanSpan logarithmicSpan h
        + representationOverhead
        + decodingOverhead
    horizonWork-linear :
      ∀ h →
      horizonWork h ≤
      EfficientOperatorMonoidRepresentation.compositionWork operatorMonoid * h
    exactness :
      ∀ (R : C.RecurrentNetwork State Input)
        (xs : ℕ → Input)
        (h : ℕ)
        (s : State) →
      C.applyEndomorphism
        (C.recurrentPrefixEndomorphism R xs h)
        s
      ＝
      C.recurrentPrefixState R xs h s
    horizonSpan-logarithmic :
      ∀ k h →
      h ≤ twoPow k →
      horizonSpan h ≤
        LogarithmicScanSpanCertificate.coefficient logarithmicSpan * k
        + LogarithmicScanSpanCertificate.additive logarithmicSpan
        + representationOverhead
        + decodingOverhead

------------------------------------------------------------------------
-- Closed MARL law composition.
--
-- These are the exact learner-facing laws used by the current coupled
-- learner: recurrent-prefix composition and the F4 optimizer step. They
-- compose with the endogenous Watkins target in one closed theorem
-- package. This is the unconditional learner-side theorem; it does not
-- claim the separate physics Law I/II/III interface is already proved.
------------------------------------------------------------------------

record CanonicalMARLLawCompositionTheorem : Set₁ where
  constructor canonicalMARLLawCompositionTheorem
  field
    recurrentPrefixComposition :
      RecurrentPrefixMonoidHomomorphism C.GRUState C.IntCode
    f4StepLaw :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (o : C.F4IntUState)
      (signal : C.IntCode) →
      C.runNetwork
        (canonicalF4RecurrentNetwork K)
        o
        signal
      ＝
      C.f4ThetaStep (C.optimizerKernel K) o signal
    watkinsSignalLaw :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (s : C.CanonicalFullLearnerState) →
      C.canonicalSignal K s ＝
      C.canonicalWatkinsTarget K s
    fullComposition :
      CanonicalGRUF4WatkinsPrefixCompositionTheorem

canonical-marl-law-composition-theorem :
  CanonicalMARLLawCompositionTheorem
canonical-marl-law-composition-theorem =
  canonicalMARLLawCompositionTheorem
    canonical-recurrent-prefix-monoid-homomorphism
    canonicalF4RecurrentNetwork-step-law
    C.canonicalSignal-watkins-target
    canonical-gruf4-watkins-prefix-composition-theorem

------------------------------------------------------------------------
-- Carrier-polymorphic continuous Hodge-Maxwell representation.
--
-- The physical content is explicit in the certificate: d F = 0 and
-- d(star F) = j, closure under the supplied solution step, exact
-- encode/decode inverse laws, recurrent-step conjugacy, and continuity.
-- This is an exact representation schema.  It does not assert existence
-- of such a certificate for the current learner without those witnesses.
------------------------------------------------------------------------

record ContinuousHodgeMaxwellExactRepresentationData
  (GRU : Set)
  {Continuous : {A B : Set} → (A → B) → Set} : Set₁ where
  constructor continuousHodgeMaxwellExactRepresentationData
  field
    Form2 : Set
    FormStar : Set
    Form3 : Set
    d : Form2 → Form3
    star : Form2 → FormStar
    dStar : FormStar → Form3
    zero3 : Form3

    Solution : Set
    fieldF : Solution → Form2
    fieldJ : Solution → Form3

    maxwellEquation :
      ∀ s →
      (d (fieldF s) ＝ zero3) ×
      (dStar (star (fieldF s)) ＝ fieldJ s)

    step : Solution → Solution
    gruStep : GRU → GRU
    encode : Solution → GRU
    decode : GRU → Solution

    decodeEncode :
      ∀ s → decode (encode s) ＝ s

    encodeDecode :
      ∀ g → encode (decode g) ＝ g

    maxwellClosed :
      ∀ s →
      maxwellEquation (step s)

    conjugacy :
      ∀ s →
      encode (step s) ＝ gruStep (encode s)

    continuousD : Continuous d
    continuousStar : Continuous star
    continuousDStar : Continuous dStar
    continuousFieldF : Continuous fieldF
    continuousFieldJ : Continuous fieldJ
    continuousStep : Continuous step
    continuousGRUStep : Continuous gruStep
    continuousEncode : Continuous encode
    continuousDecode : Continuous decode

open ContinuousHodgeMaxwellExactRepresentationData public

continuousHodgeMaxwell-state-isomorphism :
  ∀ {GRU : Set}
  {Continuous : {A B : Set} → (A → B) → Set}
  (D : ContinuousHodgeMaxwellExactRepresentationData GRU) →
  StateIsomorphism (Solution D) GRU
continuousHodgeMaxwell-state-isomorphism D =
  stateIsomorphism
    (encode D)
    (decode D)
    (decodeEncode D)
    (encodeDecode D)

continuousHodgeMaxwell-global-encode-injective :
  ∀ {GRU : Set}
  {Continuous : {A B : Set} → (A → B) → Set}
  (D : ContinuousHodgeMaxwellExactRepresentationData GRU) →
  ∀ {x y} →
  encode D x ＝ encode D y →
  x ＝ y
continuousHodgeMaxwell-global-encode-injective D {x} {y} eq =
  trans
    (sym (decodeEncode D x))
    (trans
      (ap (decode D) eq)
      (decodeEncode D y))

record ConnectedContinuousHodgeMaxwellGRURepresentationTheorem
  (GRU : Set)
  {Continuous : {A B : Set} → (A → B) → Set} : Set₁ where
  constructor connectedContinuousHodgeMaxwellGRURepresentationTheorem
  field
    semantics :
      ContinuousHodgeMaxwellExactRepresentationData GRU

    globalStateIsomorphism :
      StateIsomorphism
        (Solution semantics)
        GRU

    exactGRUStepRepresentation :
      ∀ s →
      to globalStateIsomorphism (step semantics s)
      ＝
      gruStep semantics
        (to globalStateIsomorphism s)

    exactFieldEquations :
      ∀ s →
      maxwellEquation semantics s

    globalEncodeInjective :
      ∀ {x y} →
      encode semantics x ＝ encode semantics y →
      x ＝ y

connected-continuous-hodge-maxwell-gru-representation-theorem :
  ∀ {GRU : Set}
  {Continuous : {A B : Set} → (A → B) → Set}
  (D : ContinuousHodgeMaxwellExactRepresentationData GRU) →
  ConnectedContinuousHodgeMaxwellGRURepresentationTheorem GRU
connected-continuous-hodge-maxwell-gru-representation-theorem D =
  connectedContinuousHodgeMaxwellGRURepresentationTheorem
    D
    (continuousHodgeMaxwell-state-isomorphism D)
    (λ s → conjugacy D s)
    (λ s → maxwellEquation D s)
    (continuousHodgeMaxwell-global-encode-injective D)

------------------------------------------------------------------------
-- Exact Hodge-Maxwell/full-learner bridge.
--
-- The learner side is the closed MARL law composition above.  The
-- cross-domain step is deliberately proof-relevant: a solution-state
-- encoder/decoder and exact step conjugacy are required.  The theorem then
-- derives the corresponding encoded learner-step conjugacy by equality
-- transport.  No equilibrium, convergence, or physical existence theorem
-- is smuggled into this bridge.
------------------------------------------------------------------------

record CanonicalLearnerHodgeMaxwellCompositionTheorem
  {Continuous : {A B : Set} → (A → B) → Set} : Set₁ where
  constructor canonicalLearnerHodgeMaxwellCompositionTheorem
  field
    learnerSemantics :
      CanonicalMARLLawCompositionTheorem
    hodgeRepresentation :
      ConnectedContinuousHodgeMaxwellGRURepresentationTheorem
        C.CanonicalFullLearnerState

    learnerToSolution :
      C.CanonicalFullLearnerState →
      Solution (semantics hodgeRepresentation)

    solutionToLearner :
      Solution (semantics hodgeRepresentation) →
      C.CanonicalFullLearnerState

    learnerSolutionLeftInverse :
      ∀ s →
      solutionToLearner (learnerToSolution s) ＝ s

    learnerSolutionRightInverse :
      ∀ q →
      learnerToSolution (solutionToLearner q) ＝ q

    learnerStepConjugacy :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (s : C.CanonicalFullLearnerState) →
      learnerToSolution
        (C.canonicalFullStep K s)
      ＝
      step
        (semantics hodgeRepresentation)
        (learnerToSolution s)

open CanonicalLearnerHodgeMaxwellCompositionTheorem public

canonical-learner-hodge-maxwell-step-conjugacy :
  ∀ {Continuous : {A B : Set} → (A → B) → Set}
  (W :
    CanonicalLearnerHodgeMaxwellCompositionTheorem
      {Continuous = Continuous}) →
  ∀ (K : C.CanonicalFullLearnerKernel)
  (s : C.CanonicalFullLearnerState) →
  encode
    (semantics (hodgeRepresentation W))
    (learnerToSolution W s)
  ＝
  gruStep
    (semantics (hodgeRepresentation W))
    (encode
      (semantics (hodgeRepresentation W))
      (learnerToSolution W s))
canonical-learner-hodge-maxwell-step-conjugacy
  W K s =
  trans
    (ap
      (encode (semantics (hodgeRepresentation W)))
      (sym (learnerStepConjugacy W K s)))
    (conjugacy
      (semantics (hodgeRepresentation W))
      (learnerToSolution W s))

canonical-physics-to-learner-transition-witness :
  ∀ {Continuous : {A B : Set} → (A → B) → Set}
  (W :
    CanonicalLearnerHodgeMaxwellCompositionTheorem
      {Continuous = Continuous})
  (K : C.CanonicalFullLearnerKernel) →
  PhysicsToLearnerTransitionWitness
    C.CanonicalFullLearnerState
    (Solution (semantics (hodgeRepresentation W)))
    (C.canonicalFullStep K)
    (step (semantics (hodgeRepresentation W)))
canonical-physics-to-learner-transition-witness W K =
  physicsToLearnerTransitionWitness
    (learnerToSolution W)
    (solutionToLearner W)
    (learnerSolutionLeftInverse W)
    (learnerStepConjugacy W K)

------------------------------------------------------------------------
-- nLab-guided semantic closure for the Maxwell four-law seam.
--
-- Sources:
--   Noether theorem / conserved current:
--     https://ncatlab.org/nlab/show/Noether%27s%2Btheorem
--     https://ncatlab.org/nlab/show/conserved%2Bcurrent
--   Maxwell differential-form equations / Hodge-Maxwell theorem:
--     https://ncatlab.org/nlab/show/Maxwell%27s%2Bequations
--     https://ncatlab.org/nlab/show/Hodge-Maxwell%2Btheorem
--   Action / Euler-Lagrange critical locus:
--     https://ncatlab.org/nlab/show/action%2Bfunctional
--     https://ncatlab.org/nlab/show/Euler-Lagrange%2Bequation
--
-- The repository does not expose a differential-form calculus or a
-- variational bicomplex. Therefore the external theorems are represented
-- by theorem-output interfaces rather than fabricated Agda axioms:
--
--   Noether output:
--     an on-shell conserved current for the physical step;
--   Euler-Lagrange output:
--     a variational/action semantics whose Euler-Lagrange shell contains
--     the Maxwell shell and whose critical-locus predicate is stationary.
--
-- The concrete Hodge-Maxwell representation still supplies the learner ↔
-- solution inverse and one-step conjugacy. The only semantic frontier
-- entering the four-law contract is therefore this single typed closure
-- record.
------------------------------------------------------------------------

record NLabNoetherConservationTheorem
  (PhysicalState Current : Set)
  (PhysicalStep : PhysicalState → PhysicalState)
  (MaxwellShell : PhysicalState → Set) : Set₁ where
  constructor nLabNoetherConservationTheorem
  field
    current :
      PhysicalState → Current
    conservedOnShell :
      ∀ p →
      MaxwellShell p →
      current (PhysicalStep p) ＝ current p

open NLabNoetherConservationTheorem public

record NLabEulerLagrangeMaxwellTheorem
  (PhysicalState Variation Action : Set)
  (Admissible : Variation → Set)
  (Stationary : PhysicalState → Set)
  (MaxwellShell : PhysicalState → Set) : Set₁ where
  constructor nLabEulerLagrangeMaxwellTheorem
  field
    variation :
      PhysicalState → Variation
    action :
      PhysicalState → Action
    admissibleVariation :
      ∀ p →
      Admissible (variation p)
    eulerLagrangeShell :
      PhysicalState → Set
    maxwellImpliesEulerLagrange :
      ∀ p →
      MaxwellShell p →
      eulerLagrangeShell p
    eulerLagrangeImpliesMaxwell :
      ∀ p →
      eulerLagrangeShell p →
      MaxwellShell p
    eulerLagrangeImpliesStationary :
      ∀ p →
      eulerLagrangeShell p →
      Stationary p

open NLabEulerLagrangeMaxwellTheorem public

nLabMaxwellEulerLagrangeShell-equivalence :
  ∀ {PhysicalState Variation Action : Set}
  {Admissible : Variation → Set}
  {Stationary : PhysicalState → Set}
  {MaxwellShell : PhysicalState → Set}
  (S :
    NLabEulerLagrangeMaxwellTheorem
      PhysicalState
      Variation
      Action
      Admissible
      Stationary
      MaxwellShell)
  (p : PhysicalState) →
  (MaxwellShell p → eulerLagrangeShell S p)
  ×
  (eulerLagrangeShell S p → MaxwellShell p)
nLabMaxwellEulerLagrangeShell-equivalence S p =
  ( maxwellImpliesEulerLagrange S p
  , eulerLagrangeImpliesMaxwell S p )

MaxwellSolution :
  ∀ {GRU : Set}
  {Continuous : {A B : Set} → (A → B) → Set}
  (D :
    ContinuousHodgeMaxwellExactRepresentationData
      GRU) →
  Set
MaxwellSolution D = Solution D

MaxwellShell :
  ∀ {GRU : Set}
  {Continuous : {A B : Set} → (A → B) → Set}
  (D :
    ContinuousHodgeMaxwellExactRepresentationData
      GRU) →
  MaxwellSolution D → Set
MaxwellShell D p = maxwellEquation D p

lawIFromNLabNoether :
  ∀ {LearnerState PhysicalState Current : Set}
  {physicalStepFunction : PhysicalState → PhysicalState}
  {MaxwellShell : PhysicalState → Set}
  (S :
    NLabNoetherConservationTheorem
      PhysicalState
      Current
      physicalStepFunction
      MaxwellShell)
  (shell : ∀ p → MaxwellShell p)
  (encodeD : LearnerState → PhysicalState)
  (decodeD : PhysicalState → LearnerState)
  (decodeEncodeD :
    ∀ s → decodeD (encodeD s) ＝ s) →
  LawIPhysicsWitness
    LearnerState
    PhysicalState
    Current
lawIFromNLabNoether
  {physicalStepFunction = physicalStepFunction}
  S
  shell
  encodeD
  decodeD
  decodeEncodeD =
  lawIPhysicsWitness
    encodeD
    decodeD
    decodeEncodeD
    (λ p → physicalStepFunction p)
    (current S)
    (λ p → conservedOnShell S p (shell p))

lawIIIFromNLabEulerLagrange :
  ∀ {LearnerState PhysicalState Variation Action : Set}
  {Admissible : Variation → Set}
  {Stationary : PhysicalState → Set}
  {MaxwellShell : PhysicalState → Set}
  (S :
    NLabEulerLagrangeMaxwellTheorem
      PhysicalState
      Variation
      Action
      Admissible
      Stationary
      MaxwellShell)
  (shell : ∀ p → MaxwellShell p)
  (encodeD : LearnerState → PhysicalState)
  (decodeD : PhysicalState → LearnerState)
  (decodeEncodeD :
    ∀ s → decodeD (encodeD s) ＝ s) →
  LawIIIVariationalWitness
    LearnerState
    PhysicalState
    Variation
    Action
    Admissible
    Stationary
lawIIIFromNLabEulerLagrange
  S
  shell
  encodeD
  decodeD
  decodeEncodeD =
  lawIIIVariationalWitness
    encodeD
    decodeD
    decodeEncodeD
    (variation S)
    (action S)
    (admissibleVariation S)
    (λ p →
      eulerLagrangeImpliesStationary
        S
        p
        (maxwellImpliesEulerLagrange S p (shell p)))

record NLabMaxwellSemanticClosure
  {Continuous : {A B : Set} → (A → B) → Set}
  (W :
    CanonicalLearnerHodgeMaxwellCompositionTheorem
      {Continuous = Continuous})
  (Current Variation Action : Set)
  (Admissible : Variation → Set)
  (Stationary :
    MaxwellSolution
      (semantics (hodgeRepresentation W)) → Set) : Set₁ where
  constructor nLabMaxwellSemanticClosure
  field
    noether :
      NLabNoetherConservationTheorem
        (MaxwellSolution
          (semantics (hodgeRepresentation W)))
        Current
        (step (semantics (hodgeRepresentation W)))
        (MaxwellShell
          (semantics (hodgeRepresentation W)))

    variational :
      NLabEulerLagrangeMaxwellTheorem
        (MaxwellSolution
          (semantics (hodgeRepresentation W)))
        Variation
        Action
        Admissible
        Stationary
        (MaxwellShell
          (semantics (hodgeRepresentation W)))

open NLabMaxwellSemanticClosure public

nLabMaxwellFourLawOneStep :
  ∀ {Continuous : {A B : Set} → (A → B) → Set}
  (W :
    CanonicalLearnerHodgeMaxwellCompositionTheorem
      {Continuous = Continuous})
  (K : C.CanonicalFullLearnerKernel)
  {Current Variation Action : Set}
  {Admissible : Variation → Set}
  {Stationary :
    MaxwellSolution
      (semantics (hodgeRepresentation W)) → Set} →
  NLabMaxwellSemanticClosure
    W
    Current
    Variation
    Action
    Admissible
    Stationary →
  FourLawOneStepWitnessContract
    C.CanonicalFullLearnerState
    (MaxwellSolution
      (semantics (hodgeRepresentation W)))
    Current
    Variation
    Action
    Admissible
    Stationary
    (C.canonicalFullStep K)
    (step (semantics (hodgeRepresentation W)))
nLabMaxwellFourLawOneStep
  W
  K
  S =
  fourLawOneStepWitnessContract
    (lawIFromNLabNoether
      (noether S)
      (λ p →
        maxwellEquation
          (semantics (hodgeRepresentation W))
          p)
      (learnerToSolution W)
      (solutionToLearner W)
      (learnerSolutionLeftInverse W))
    (lawIIIFromNLabEulerLagrange
      (variational S)
      (λ p →
        maxwellEquation
          (semantics (hodgeRepresentation W))
          p)
      (learnerToSolution W)
      (solutionToLearner W)
      (learnerSolutionLeftInverse W))
    (canonical-physics-to-learner-transition-witness W K)

------------------------------------------------------------------------
-- A semantically closed four-law model is the single proof-relevant
-- downstream boundary.  Once this package is inhabited, callers do not
-- repeat the Noether, variational, shell, inverse, or transition premises.
--
-- This does not manufacture an inhabitant: the repository's generic
-- impossibility boundary rules out a constructor that could populate these
-- fields for arbitrary predicates.  The package therefore concentrates the
-- unavoidable physical semantics into one explicit object while keeping all
-- later transport theorems premise-free.
------------------------------------------------------------------------

record NLabMaxwellFourLawSemanticallyClosed
  {Continuous : {A B : Set} → (A → B) → Set}
  (W :
    CanonicalLearnerHodgeMaxwellCompositionTheorem
      {Continuous = Continuous})
  (Current Variation Action : Set)
  (Admissible : Variation → Set)
  (Stationary :
    MaxwellSolution
      (semantics (hodgeRepresentation W)) → Set) : Set₁ where
  constructor nLabMaxwellFourLawSemanticallyClosed
  field
    kernel : C.CanonicalFullLearnerKernel
    semanticClosure :
      NLabMaxwellSemanticClosure
        W
        Current
        Variation
        Action
        Admissible
        Stationary

nLabMaxwellFourLawSemanticallyClosed-from-semantic :
  ∀ {Continuous : {A B : Set} → (A → B) → Set}
  (W :
    CanonicalLearnerHodgeMaxwellCompositionTheorem
      {Continuous = Continuous})
  (K : C.CanonicalFullLearnerKernel)
  {Current Variation Action : Set}
  {Admissible : Variation → Set}
  {Stationary :
    MaxwellSolution
      (semantics (hodgeRepresentation W)) → Set}
  (S :
    NLabMaxwellSemanticClosure
      W
      Current
      Variation
      Action
      Admissible
      Stationary) →
  NLabMaxwellFourLawSemanticallyClosed
    W
    Current
    Variation
    Action
    Admissible
    Stationary
nLabMaxwellFourLawSemanticallyClosed-from-semantic
  W
  K
  S =
  nLabMaxwellFourLawSemanticallyClosed
    K
    S

open NLabMaxwellFourLawSemanticallyClosed public

nLabMaxwellFourLawOneStepClosed :
  ∀ {Continuous : {A B : Set} → (A → B) → Set}
  {W :
    CanonicalLearnerHodgeMaxwellCompositionTheorem
      {Continuous = Continuous}}
  {Current Variation Action : Set}
  {Admissible : Variation → Set}
  {Stationary :
    MaxwellSolution
      (semantics (hodgeRepresentation W)) → Set}
  (B :
    NLabMaxwellFourLawSemanticallyClosed
      W
      Current
      Variation
      Action
      Admissible
      Stationary) →
  FourLawOneStepWitnessContract
    C.CanonicalFullLearnerState
    (MaxwellSolution
      (semantics (hodgeRepresentation W)))
    Current
    Variation
    Action
    Admissible
    Stationary
    (C.canonicalFullStep (kernel B))
    (step (semantics (hodgeRepresentation W)))
nLabMaxwellFourLawOneStepClosed {W = W} B =
  nLabMaxwellFourLawOneStep
    W
    (kernel B)
    (semanticClosure B)

------------------------------------------------------------------------
-- Once the nLab semantic square is inhabited, autonomous-time transport
-- is already closed by the existing one-step conjugacy kernel.
------------------------------------------------------------------------

nLabMaxwellIterateConjugacy :
  ∀ {Continuous : {A B : Set} → (A → B) → Set}
  (W :
    CanonicalLearnerHodgeMaxwellCompositionTheorem
      {Continuous = Continuous})
  (K : C.CanonicalFullLearnerKernel) →
  ∀ n s →
  learnerToSolution W
    (iterateStep
      (C.canonicalFullStep K)
      n
      s)
  ＝
  iterateStep
    (step (semantics (hodgeRepresentation W)))
    n
    (learnerToSolution W s)
nLabMaxwellIterateConjugacy
  W
  K
  n
  s =
  iterateConjugacy
    (learnerToSolution W)
    (λ s →
      learnerStepConjugacy W K s)
    n
    s

nLabMaxwellIterateConjugacyClosed :
  ∀ {Continuous : {A B : Set} → (A → B) → Set}
  {W :
    CanonicalLearnerHodgeMaxwellCompositionTheorem
      {Continuous = Continuous}}
  {Current Variation Action : Set}
  {Admissible : Variation → Set}
  {Stationary :
    MaxwellSolution
      (semantics (hodgeRepresentation W)) → Set}
  (B :
    NLabMaxwellFourLawSemanticallyClosed
      W
      Current
      Variation
      Action
      Admissible
      Stationary) →
  ∀ n s →
  learnerToSolution W
    (iterateStep
      (C.canonicalFullStep (kernel B))
      n
      s)
  ＝
  iterateStep
    (step (semantics (hodgeRepresentation W)))
    n
    (learnerToSolution W s)
nLabMaxwellIterateConjugacyClosed {W = W} B n s =
  nLabMaxwellIterateConjugacy
    W
    (kernel B)
    n
    s

------------------------------------------------------------------------
-- Single-file algebraic consistency package.
--
-- The statistical Law-IV representation and the nLab-guided four-law
-- witness are already proved independently.  This package composes those
-- existing proofs in this monolith: GRU injectivity, the closed four-law
-- witness, one-step physics/learner transport, and exact iterate transport.
-- It adds no physical inhabitant and no new axiom; an instance still requires
-- the explicit semantic closure B above.
------------------------------------------------------------------------

record NLabMaxwellFourLawGRUAlgebraicConsistencyTheorem
  {Continuous : {A B : Set} → (A → B) → Set}
  {W :
    CanonicalLearnerHodgeMaxwellCompositionTheorem
      {Continuous = Continuous}}
  {Current Variation Action : Set}
  {Admissible : Variation → Set}
  {Stationary :
    MaxwellSolution
      (semantics (hodgeRepresentation W)) → Set}
  (B :
    NLabMaxwellFourLawSemanticallyClosed
      W
      Current
      Variation
      Action
      Admissible
      Stationary) : Set₁ where
  constructor nLabMaxwellFourLawGRUAlgebraicConsistencyTheorem
  field
    statisticalRepresentation :
      CanonicalGRUStatisticalInjectivityTheorem
    statisticalInjective :
      ∀ {s t : C.GRUState} →
      canonicalGRUStatisticalEncode s ＝
      canonicalGRUStatisticalEncode t →
      s ＝ t
    statisticalStep :
      ∀ (s : C.GRUState) (x : C.IntCode) →
      canonicalGRUStatisticalEncode (C.gruStep s x)
      ＝
      (C.gruStep s x ,
       (λ _ → C.hiddenState (C.gruStep s x)))
    fourLaw :
      FourLawOneStepWitnessContract
        C.CanonicalFullLearnerState
        (MaxwellSolution
          (semantics (hodgeRepresentation W)))
        Current
        Variation
        Action
        Admissible
        Stationary
        (C.canonicalFullStep (kernel B))
        (step (semantics (hodgeRepresentation W)))
    learnerSemantics :
      CanonicalMARLLawCompositionTheorem
    representation :
      ConnectedContinuousHodgeMaxwellGRURepresentationTheorem
        C.CanonicalFullLearnerState
    iterateTransport :
      ∀ n s →
      learnerToSolution W
        (iterateStep
          (C.canonicalFullStep (kernel B))
          n
          s)
      ＝
      iterateStep
        (step (semantics (hodgeRepresentation W)))
        n
        (learnerToSolution W s)

nLabMaxwellFourLawGRUAlgebraicConsistencyTheorem-from-closed :
  ∀ {Continuous : {A B : Set} → (A → B) → Set}
  {W :
    CanonicalLearnerHodgeMaxwellCompositionTheorem
      {Continuous = Continuous}}
  {Current Variation Action : Set}
  {Admissible : Variation → Set}
  {Stationary :
    MaxwellSolution
      (semantics (hodgeRepresentation W)) → Set}
  (B :
    NLabMaxwellFourLawSemanticallyClosed
      W
      Current
      Variation
      Action
      Admissible
      Stationary) →
  NLabMaxwellFourLawGRUAlgebraicConsistencyTheorem B
nLabMaxwellFourLawGRUAlgebraicConsistencyTheorem-from-closed {W = W} B =
  nLabMaxwellFourLawGRUAlgebraicConsistencyTheorem
    canonical-gru-statistical-injectivity-theorem
    canonicalGRUStatisticalEncodeInjective
    canonicalGRUStatisticalStepConsequence
    (nLabMaxwellFourLawOneStepClosed B)
    (learnerSemantics W)
    (hodgeRepresentation W)
    (nLabMaxwellIterateConjugacyClosed B)


------------------------------------------------------------------------
-- Repository-wide semantic e-graph/A* closure.
--
-- Every surviving Agda module can be placed in an indexed semantic family.
-- The closure is unconditional at that semantic layer: any supplied sound
-- interpretation and any sound e-graph path produce exact equality.
-- A* costs remain search metadata, never proof evidence.
------------------------------------------------------------------------

canonical-repository-wide-agda-egraph-astar-closure :
  (F : AgdaSemanticModuleFamily)
  (m : RepositoryAgdaModule)
  {e f : Expression F m} →
  EGraphSemanticPath
    (semantics (closure F m))
    e
    f →
  interpret (semantics (closure F m)) e
  ＝
  interpret (semantics (closure F m)) f
canonical-repository-wide-agda-egraph-astar-closure =
  repositoryAgdaAStarSemanticClosure

canonical-unconditional-agda-egraph-astar-closure :
  UnconditionalAgdaEGraphAStarClosure
canonical-unconditional-agda-egraph-astar-closure =
  unconditional-agda-egraph-astar-closure


------------------------------------------------------------------------

f4-add-right-nonnegative :
  ∀ (n m : ℕ) → n ≤ n + m
f4-add-right-nonnegative n zero = ≤-refl n
f4-add-right-nonnegative n (succ m) =
  ≤-trans n (n + m) (succ (n + m))
    (f4-add-right-nonnegative n m)
    (≤-succ (n + m))

record MegaGeneralizedWalrasianEquilibrium
  (State Price Allocation : Set) : Set₁ where
  constructor megaGeneralizedWalrasianEquilibrium
  field
    aggregate : (State → Allocation) → Allocation
    equilibrium : Price → Allocation → Set
    characterization : Price → Allocation → Set
    characterizationBridge :
      ∀ {p a} →
      characterization p a →
      equilibrium p a

open MegaGeneralizedWalrasianEquilibrium public

record GeneralizedWalrasianData
  (Agent Commodity Price Allocation : Set) : Set₁ where
  constructor generalizedWalrasianData
  field
    consumption : Agent → Set
    preference : Agent → Allocation → Allocation → Set
    budget : Price → Agent → Allocation → Set
    feasible : Allocation → Set
    marketClearing : Price → Allocation → Set
    equilibrium : Price → Allocation → Set
    characterization : Price → Allocation → Set
    characterizationFromEquilibrium :
      ∀ {p a} →
      equilibrium p a →
      characterization p a

open GeneralizedWalrasianData public

FiniteNonIIDPreference :
  ∀ {Agent Good : Set}
  (utility : Agent → (Good → ℕ) → ℕ) →
  Agent → (Agent → Good → ℕ) → (Agent → Good → ℕ) → Set
FiniteNonIIDPreference utility i x y =
  utility i (x i) ≤ utility i (y i)

record FiniteNonIIDGeneralizedEquilibrium
  (Agent Good : Set)
  (agents : List Agent)
  (goods : List Good)
  (utility : Agent → (Good → ℕ) → ℕ)
  (endowment : Agent → Good → ℕ)
  (price : Good → ℕ)
  (allocation : Agent → Good → ℕ) : Set₁ where
  constructor finiteNonIIDGeneralizedEquilibrium
  field
    budgetOptimal :
      ∀ i bundle →
      BudgetFeasible
        goods
        price
        (endowment i)
        bundle →
      utility i bundle ≤
      utility i (allocation i)
    marketClearing :
      ∀ g →
      sumNat (map (λ i → allocation i g) agents) ＝
      sumNat (map (λ i → endowment i g) agents)

-- A Pareto improvement weakly benefits every agent and strictly benefits
-- at least one. The argument order is candidate allocation, then baseline.
record MegaParetoImprovement
  (Agent Allocation : Set)
  (weakPreference strictPreference :
    Agent → Allocation → Allocation → Set)
  (candidate baseline : Allocation) : Set₁ where
  constructor megaParetoImprovement
  field
    weaklyBetter :
      ∀ i → weakPreference i baseline candidate
    strictlyBetter :
      Σ Agent (λ i → strictPreference i candidate baseline)

open MegaParetoImprovement public

megaParetoOptimal :
  ∀ {Agent Allocation : Set}
  {weakPreference strictPreference :
    Agent → Allocation → Allocation → Set}
  (feasible : Allocation → Set) →
  Allocation → Set₁
megaParetoOptimal
  {Agent}
  {Allocation}
  {weakPreference}
  {strictPreference}
  feasible
  a =
  feasible a ×
  (∀ {b : Allocation} →
   feasible b →
   MegaParetoImprovement
     Agent
     Allocation
     weakPreference
     strictPreference
     b
     a →
   ⊥)

record MegaFirstWelfareTheoremConditions
  (Agent Price Allocation : Set)
  (weakPreference strictPreference :
    Agent → Allocation → Allocation → Set)
  (feasible : Allocation → Set)
  (budget : Price → Agent → Allocation → Set)
  (equilibrium : Price → Allocation → Set)
  (p : Price)
  (a : Allocation) : Set₁ where
  constructor megaFirstWelfareTheoremConditions
  field
    equilibriumWitness :
      equilibrium p a
    feasibleWitness :
      feasible a
    noStrictAffordableAlternative :
      ∀ i b →
      budget p i b →
      ¬ strictPreference i b a
    paretoImprovementAffordability :
      ∀ {b : Allocation} →
      feasible b →
      (improvement :
        MegaParetoImprovement
          Agent
          Allocation
          weakPreference
          strictPreference
          b
          a) →
      budget p
        (pr₁ (strictlyBetter improvement))
        b

open MegaFirstWelfareTheoremConditions public

megaNatNoStrictBack :
  ∀ {n : ℕ} →
  succ n ≤ n →
  ⊥
megaNatNoStrictBack {zero} ()
megaNatNoStrictBack {succ n} h =
  megaNatNoStrictBack h

megaNatStrictCostContradiction :
  ∀ {m n : ℕ} →
  n ≤ m →
  m < n →
  ⊥
megaNatStrictCostContradiction hle hlt =
  megaNatNoStrictBack (≤-trans hlt hle)

-- Demand/cost closure needed by the welfare-boundary arguments.
-- Preference improvement must force a strictly higher cost; affordability
-- must keep the candidate's cost below the baseline allocation's cost.
record MegaDemandCostKernel
  (Agent Price Allocation : Set)
  (weakPreference strictPreference :
    Agent → Allocation → Allocation → Set)
  (feasible : Allocation → Set)
  (budget : Price → Agent → Allocation → Set)
  (equilibrium : Price → Allocation → Set)
  (cost : Price → Agent → Allocation → ℕ)
  (p : Price)
  (a : Allocation) : Set₁ where
  constructor megaDemandCostKernel
  field
    equilibriumWitness : equilibrium p a
    feasibleWitness : feasible a
    preferredCostly :
      ∀ i x y → weakPreference i x y → cost p i y ≤ cost p i x
    strictlyPreferredCostly :
      ∀ i x y → strictPreference i x y → cost p i y < cost p i x
    budgetCostBound :
      ∀ i b → budget p i b → cost p i b ≤ cost p i a
    paretoImprovementAffordability :
      ∀ {b : Allocation} →
      feasible b →
      (improvement : MegaParetoImprovement
        Agent Allocation weakPreference strictPreference b a) →
      budget p (pr₁ (strictlyBetter improvement)) b

open MegaDemandCostKernel public

megaNoStrictAffordableAlternative-from-demand-cost :
  ∀ {Agent Price Allocation : Set}
  {weakPreference strictPreference :
    Agent → Allocation → Allocation → Set}
  {feasible : Allocation → Set}
  {budget : Price → Agent → Allocation → Set}
  {equilibrium : Price → Allocation → Set}
  {cost : Price → Agent → Allocation → ℕ}
  {p : Price}
  {a : Allocation} →
  MegaDemandCostKernel
    Agent
    Price
    Allocation
    weakPreference
    strictPreference
    feasible
    budget
    equilibrium
    cost
    p
    a →
  ∀ i b →
  budget p i b →
  ¬ strictPreference i b a
megaNoStrictAffordableAlternative-from-demand-cost kernel i b affordable =
  λ strictlyPreferred →
    megaNatStrictCostContradiction
      (budgetCostBound kernel i b affordable)
      (strictlyPreferredCostly kernel i b strictlyPreferred)

FiniteNonIIDStrictPreference :
  ∀ {Agent Good : Set}
  (utility : Agent → (Good → ℕ) → ℕ) →
  Agent → (Agent → Good → ℕ) → (Agent → Good → ℕ) → Set
FiniteNonIIDStrictPreference utility i x y =
  utility i (y i) < utility i (x i)

record FiniteNonIIDDemandCostClosure
  (Agent Good : Set)
  (agents : List Agent)
  (goods : List Good)
  (utility : Agent → (Good → ℕ) → ℕ)
  (endowment : Agent → Good → ℕ)
  (price : Good → ℕ)
  (allocation : Agent → Good → ℕ) : Set₁ where
  constructor finiteNonIIDDemandCostClosure
  field
    equilibriumWitness :
      FiniteNonIIDGeneralizedEquilibrium
        Agent
        Good
        agents
        goods
        utility
        endowment
        price
        allocation

    preferredCostly :
      ∀ i x y →
      utility i (x i) ≤ utility i (y i) →
      bundleCost goods price (y i) ≤
      bundleCost goods price (x i)

    strictlyPreferredCostly :
      ∀ i x y →
      utility i (y i) < utility i (x i) →
      bundleCost goods price (y i) <
      bundleCost goods price (x i)

    paretoImprovementAffordability :
      ∀ {b : Agent → Good → ℕ} →
      (improvement :
        MegaParetoImprovement
          Agent
          (Agent → Good → ℕ)
          (FiniteNonIIDPreference utility)
          (FiniteNonIIDStrictPreference utility)
          b
          allocation) →
      BudgetFeasible
        goods
        price
        (endowment
          (pr₁ (strictlyBetter improvement)))
        b

finiteNonIIDBudgetCostBound :
  ∀ {Agent Good : Set}
  {goods : List Good}
  {price : Good → ℕ}
  {endowment : Agent → Good → ℕ}
  {i : Agent}
  {bundle : Good → ℕ} →
  BudgetFeasible goods price (endowment i) bundle →
  bundleCost goods price bundle ≤
  bundleCost goods price (endowment i)
finiteNonIIDBudgetCostBound affordable = affordable

finiteNonIIDDemandCostKernel :
  ∀ {Agent Good : Set}
  {agents : List Agent}
  {goods : List Good}
  {utility : Agent → (Good → ℕ) → ℕ}
  {endowment : Agent → Good → ℕ}
  {price : Good → ℕ}
  {allocation : Agent → Good → ℕ} →
  FiniteNonIIDDemandCostClosure
    Agent
    Good
    agents
    goods
    utility
    endowment
    price
    allocation →
  MegaDemandCostKernel
    Agent
    (Good → ℕ)
    (Agent → Good → ℕ)
    (FiniteNonIIDPreference utility)
    (FiniteNonIIDStrictPreference utility)
    (λ a →
      ∀ g →
      sumNat (map (λ i → a i g) agents) ＝
      sumNat (map (λ i → endowment i g) agents))
    (λ p i bundle → BudgetFeasible goods p (endowment i) bundle)
    (λ p a →
      FiniteNonIIDGeneralizedEquilibrium
        Agent
        Good
        agents
        goods
        utility
        endowment
        p
        a)
    (λ p i bundle → bundleCost goods p (bundle i))
    price
    allocation
finiteNonIIDDemandCostKernel closure =
  megaDemandCostKernel
    (equilibriumWitness closure)
    (marketClearing (equilibriumWitness closure))
    (λ i b preferred →
      preferredCostly closure i b allocation preferred)
    (λ i b strictlyPreferred →
      strictlyPreferredCostly closure i b allocation strictlyPreferred)
    (λ i b affordable →
      finiteNonIIDBudgetCostBound affordable)
    (λ {b} _ improvement →
      paretoImprovementAffordability closure improvement)

record MegaSecondWelfareTheoremBoundaryCounterexample : Set₁ where
  constructor megaSecondWelfareTheoremBoundaryCounterexample
  field
    Price : Set
    Allocation : Set
    paretoOptimal : Allocation → Set₁
    equilibrium : Price → Allocation → Set
    allocationWitness : Allocation
    paretoWitness :
      paretoOptimal allocationWitness
    noSupportingPrice :
      ¬ Σ Price (λ p → equilibrium p allocationWitness)

open MegaSecondWelfareTheoremBoundaryCounterexample public

megaSecondWelfareTheorem-boundary-counterexample :
  MegaSecondWelfareTheoremBoundaryCounterexample
megaSecondWelfareTheorem-boundary-counterexample =
  megaSecondWelfareTheoremBoundaryCounterexample
    ⊥
    ⊤
    (λ _ → ⊤)
    (λ _ _ → ⊥)
    tt
    tt
    (λ { (_ , e) → e })

record MegaNoStrictAffordableAlternativeBoundary
  (Agent Price Allocation : Set)
  (strictPreference :
    Agent → Allocation → Allocation → Set)
  (budget : Price → Agent → Allocation → Set)
  (p : Price)
  (a : Allocation) : Set₁ where
  constructor megaNoStrictAffordableAlternativeBoundary
  field
    demandOptimality :
      ∀ i b →
      budget p i b →
      ¬ strictPreference i b a

megaNoStrictAffordableAlternative-is-demand-optimality :
  ∀ {Agent Price Allocation : Set}
  {strictPreference :
    Agent → Allocation → Allocation → Set}
  {budget : Price → Agent → Allocation → Set}
  {p : Price} {a : Allocation} →
  MegaNoStrictAffordableAlternativeBoundary
    Agent Price Allocation strictPreference budget p a →
  (∀ i b →
    budget p i b →
    ¬ strictPreference i b a)
megaNoStrictAffordableAlternative-is-demand-optimality boundary =
  MegaNoStrictAffordableAlternativeBoundary.demandOptimality boundary

GeneralizedWalrasianEquilibrium :
  Set → Set → Set → Set₁
GeneralizedWalrasianEquilibrium =
  MegaGeneralizedWalrasianEquilibrium

generalizedWalrasianEquilibrium :
  ∀ {State Price Allocation : Set} →
  (encode : State → Price) →
  (equilibrium : Price → Allocation → Set) →
  (feasibility : Price → Allocation → Set) →
  (characterize :
    ∀ {p a} →
    equilibrium p a →
    feasibility p a) →
  GeneralizedWalrasianEquilibrium State Price Allocation
generalizedWalrasianEquilibrium =
  megaGeneralizedWalrasianEquilibrium

ProductionSet : Set → Set
ProductionSet ProductionPlan = ProductionPlan → Set

record CompetitiveProductionEconomy
  (Agent Firm Commodity Price Consumption ProductionPlan : Set) : Set₁ where
  constructor competitiveProductionEconomy
  field
    endowment : Agent → Consumption
    preference : Agent → Consumption → Consumption → Set
    consumptionFeasible : Agent → Consumption → Set
    productionSet : Firm → ProductionPlan → Set
    ownershipShare : Agent → Firm → Set
    profitMaximization :
      Firm → Price → ProductionPlan → Set
    resourceBalance :
      Commodity → Set

record CompetitiveWalrasianEquilibriumWithProduction
  (Agent Firm Commodity Price Consumption ProductionPlan : Set)
  (E : CompetitiveProductionEconomy
    Agent Firm Commodity Price Consumption ProductionPlan) : Set₁ where
  constructor competitiveWalrasianEquilibriumWithProduction
  field
    price : Price
    consumption : Agent → Consumption
    production : Firm → ProductionPlan
    consumerOptimality :
      ∀ i →
      CompetitiveProductionEconomy.preference E i
        (consumption i)
        (consumption i)
    productionFeasibility :
      ∀ j →
      CompetitiveProductionEconomy.productionSet E
        j
        (production j)
    productionOptimality :
      ∀ j →
      CompetitiveProductionEconomy.profitMaximization E
        j
        price
        (production j)
    consumptionFeasibility :
      ∀ i →
      CompetitiveProductionEconomy.consumptionFeasible E
        i
        (consumption i)
    marketClearing :
      ∀ c →
      CompetitiveProductionEconomy.resourceBalance E c

record ProductionFeasibilityWitness
  (Firm ProductionPlan : Set)
  (feasible : Firm → ProductionPlan → Set)
  (production : Firm → ProductionPlan) : Set₁ where
  constructor productionFeasibilityWitness
  field
    witness :
      ∀ j →
      feasible j (production j)

record FirmProfitOptimalityWitness
  (Firm Price ProductionPlan : Set)
  (optimal : Firm → Price → ProductionPlan → Set)
  (price : Price)
  (production : Firm → ProductionPlan) : Set₁ where
  constructor firmProfitOptimalityWitness
  field
    witness :
      ∀ j →
      optimal j price (production j)

record ConsumerOptimalityWitness
  (Agent Consumption : Set)
  (optimal : Agent → Consumption → Set)
  (consumption : Agent → Consumption) : Set₁ where
  constructor consumerOptimalityWitness
  field
    witness :
      ∀ i →
      optimal i (consumption i)

record ConsumptionFeasibilityWitness
  (Agent Consumption : Set)
  (feasible : Agent → Consumption → Set)
  (consumption : Agent → Consumption) : Set₁ where
  constructor consumptionFeasibilityWitness
  field
    witness :
      ∀ i →
      feasible i (consumption i)

record AggregateFeasibilityWitness
  (Allocation : Set)
  (feasible : Allocation → Set)
  (allocation : Allocation) : Set₁ where
  constructor aggregateFeasibilityWitness
  field
    witness :
      feasible allocation

record MarketClearingWitness
  (Price Allocation : Set)
  (marketClearing : Price → Allocation → Set)
  (price : Price)
  (allocation : Allocation) : Set₁ where
  constructor marketClearingWitness
  field
    witness :
      marketClearing price allocation

record SupportingPriceWitness
  (Price Allocation : Set)
  (supports : Price → Allocation → Set)
  (price : Price)
  (allocation : Allocation) : Set₁ where
  constructor supportingPriceWitness
  field
    witness :
      supports price allocation

record FactorTransitionWitness
  (State Factor : Set)
  (step : State → State)
  (observe : State → Factor) : Set₁ where
  constructor factorTransitionWitness
  field
    factorStep : Factor → Factor
    observe-step :
      ∀ s →
      observe (step s) ＝
      factorStep (observe s)

open FactorTransitionWitness public

factorTransitionAfterIterate :
  ∀ {State Factor : Set}
  {step : State → State}
  {observe : State → Factor}
  (W :
    FactorTransitionWitness
      State
      Factor
      step
      observe)
  (n : ℕ)
  (s : State) →
  observe (iterateIsomorphism step n s) ＝
  iterateIsomorphism (factorStep W) n (observe s)
factorTransitionAfterIterate W zero s =
  refl
factorTransitionAfterIterate W (succ n) s =
  trans
    (factorTransitionAfterIterate W n (step s))
    (ap
      (iterateIsomorphism (factorStep W) n)
      (observe-step W s))

record RelationFactorTransitionWitness
  (State Factor : Set)
  (step : State → State)
  (related : State → State → Set)
  (observe : State → Factor) : Set₁ where
  constructor relationFactorTransitionWitness
  field
    transition :
      FactorTransitionWitness
        State
        Factor
        step
        observe
    observeRespects :
      ∀ {s t} →
      related s t →
      observe s ＝ observe t
    relationStepPreserved :
      ∀ {s t} →
      related s t →
      related
        (step s)
        (step t)

record RecursiveRadnerData
  (State Agent Commodity Asset Price Allocation Portfolio : Set)
  (priceProcess : State → Price)
  (allocationProcess : State → Agent → Allocation)
  (portfolioProcess : State → Agent → Portfolio) : Set₁ where
  constructor recursiveRadnerData
  field
    transition : State → State
    feasible : State → Agent → Allocation → Portfolio → Set
    optimal : State → Agent → Allocation → Portfolio → Set
    commodityMarketClearing : State → Set
    assetMarketClearing : State → Set
    priceRecursion : State → Price → Set
    allocationRecursion : State → Agent → Allocation → Set
    portfolioRecursion : State → Agent → Portfolio → Set

record RecursiveRadnerEquilibrium
  (State Agent Commodity Asset Price Allocation Portfolio : Set)
  (priceProcess : State → Price)
  (allocationProcess : State → Agent → Allocation)
  (portfolioProcess : State → Agent → Portfolio)
  (D :
    RecursiveRadnerData
      State Agent Commodity Asset Price Allocation Portfolio
      priceProcess
      allocationProcess
      portfolioProcess) : Set₁ where
  constructor recursiveRadnerEquilibrium
  field
    feasibility :
      ∀ s i →
      RecursiveRadnerData.feasible D
        s i
        (allocationProcess s i)
        (portfolioProcess s i)

    optimality :
      ∀ s i →
      RecursiveRadnerData.optimal D
        s i
        (allocationProcess s i)
        (portfolioProcess s i)

    commodityClearing :
      ∀ s →
      RecursiveRadnerData.commodityMarketClearing D s

    assetClearing :
      ∀ s →
      RecursiveRadnerData.assetMarketClearing D s

    priceRecursionWitness :
      ∀ s →
      RecursiveRadnerData.priceRecursion D
        s
        (priceProcess s)

    allocationRecursionWitness :
      ∀ s i →
      RecursiveRadnerData.allocationRecursion D
        s i
        (allocationProcess s i)

    portfolioRecursionWitness :
      ∀ s i →
      RecursiveRadnerData.portfolioRecursion D
        s i
        (portfolioProcess s i)

record RecursiveRadnerExistence
  (State Agent Commodity Asset Price Allocation Portfolio : Set) : Set₁ where
  constructor recursiveRadnerExistence
  field
    priceProcess : State → Price
    allocationProcess : State → Agent → Allocation
    portfolioProcess : State → Agent → Portfolio

    radnerData :
      RecursiveRadnerData
        State Agent Commodity Asset Price Allocation Portfolio
        priceProcess
        allocationProcess
        portfolioProcess

    equilibrium :
      RecursiveRadnerEquilibrium
        State Agent Commodity Asset Price Allocation Portfolio
        priceProcess
        allocationProcess
        portfolioProcess
        radnerData

RecursiveRadnerPrice :
  ∀ {State Price : Set} →
  Set
RecursiveRadnerPrice {State} {Price} =
  State → Price

RecursiveRadnerAllocation :
  ∀ {State Agent Allocation Portfolio : Set} →
  Set
RecursiveRadnerAllocation {State} {Agent} {Allocation} {Portfolio} =
  (State → Agent → Allocation)
  ×
  (State → Agent → Portfolio)

recursiveRadner-generalized :
  ∀ {State Agent Commodity Asset Price Allocation Portfolio : Set} →
  MegaGeneralizedWalrasianEquilibrium
    State
    RecursiveRadnerPrice
    (RecursiveRadnerAllocation
      {State = State}
      {Agent = Agent}
      {Allocation = Allocation}
      {Portfolio = Portfolio})
recursiveRadner-generalized
  {State}
  {Agent}
  {Commodity}
  {Asset}
  {Price}
  {Allocation}
  {Portfolio} =
  megaGeneralizedWalrasianEquilibrium
    (λ x → x)
    (λ pricePair allocationPair →
      Σ (RecursiveRadnerData
          State
          Agent
          Commodity
          Asset
          Price
          Allocation
          Portfolio
          (pr₁ allocationPair)
          (pr₂ allocationPair))
        (λ D →
          RecursiveRadnerEquilibrium
            State
            Agent
            Commodity
            Asset
            Price
            Allocation
            Portfolio
            (pr₁ allocationPair)
            (pr₂ allocationPair)
            D))
    (λ pricePair allocationPair →
      Σ (RecursiveRadnerData
          State
          Agent
          Commodity
          Asset
          Price
          Allocation
          Portfolio
          (pr₁ allocationPair)
          (pr₂ allocationPair))
        (λ D →
          RecursiveRadnerEquilibrium
            State
            Agent
            Commodity
            Asset
            Price
            Allocation
            Portfolio
            (pr₁ allocationPair)
            (pr₂ allocationPair)
            D))
    (λ {pricePair} {allocationPair} h → h)

megaNoEquilibriumGeneralizedWalrasian :
  MegaGeneralizedWalrasianEquilibrium ⊤ ⊤ ⊤
megaNoEquilibriumGeneralizedWalrasian =
  megaGeneralizedWalrasianEquilibrium
    (λ _ → tt)
    (λ _ _ → ⊥)
    (λ _ _ → ⊥)
    (λ ())

megaNoEquilibriumWitness :
  ¬ Σ ⊤
    (λ p → Σ ⊤
      (λ a →
        equilibrium
          megaNoEquilibriumGeneralizedWalrasian
          p
          a))
megaNoEquilibriumWitness
  (p , a , witness) =
  witness

noUnconditionalMegaGeneralizedWalrasianExistence :
  ¬
    (∀ {State Price Allocation : Set}
      (D : MegaGeneralizedWalrasianEquilibrium
        State Price Allocation) →
      Σ Price
        (λ p →
          Σ Allocation
            (λ a → equilibrium D p a)))
noUnconditionalMegaGeneralizedWalrasianExistence
  theorem =
  megaNoEquilibriumWitness
    (theorem megaNoEquilibriumGeneralizedWalrasian)

-- A global Walrasian square carries two aggregate interpretations and
-- explicit round-trip maps through price and allocation representations.
-- The three fields are obligations: aggregate agreement and both retractions.
record MegaWalrasianGlobalSquareConjugacy
  (State Price Allocation : Set)
  (sourceAggregate targetAggregate :
    (State → Allocation) → Allocation)
  (priceOf : State → Price)
  (stateOfPrice : Price → State)
  (allocationOf : State → Allocation)
  (stateOfAllocation : Allocation → State) : Set₁ where
  constructor megaWalrasianGlobalSquareConjugacy
  field
    aggregateConjugacy :
      ∀ f → sourceAggregate f ＝ targetAggregate f
    priceRoundTrip :
      ∀ s → stateOfPrice (priceOf s) ＝ s
    allocationRoundTrip :
      ∀ s → stateOfAllocation (allocationOf s) ＝ s

open MegaWalrasianGlobalSquareConjugacy public

megaNoEquilibriumWalrasianSquare :
  MegaWalrasianGlobalSquareConjugacy
    ⊤
    ⊤
    ⊤
    (λ _ → tt)
    (λ _ → tt)
    (λ x → x)
    (λ x → x)
    (λ x → x)
    (λ x → x)
megaNoEquilibriumWalrasianSquare =
  megaWalrasianGlobalSquareConjugacy
    (λ _ → refl)
    (λ _ → refl)
    (λ _ → refl)

------------------------------------------------------------------------
-- Generic strict-progress and carrier-polymorphic frontier core.
-- Kept in this monolith so there is one authoritative theorem source.
------------------------------------------------------------------------



record StrictProgressWitness
  (State Measure : Set)
  (step : State → State)
  (_<_ : Measure → Measure → Set) : Set₁ where
  constructor strictProgressWitness
  field
    measure : State → Measure
    stepProgress :
      ∀ s →
      measure s < measure (step s)
    strictProgressTransitive :
      ∀ {a b c} →
      a < b →
      b < c →
      a < c
    strictProgressIrreflexive :
      ∀ a → ¬ (a < a)

record StrictProgressRelation
  (Measure : Set)
  (_<_ : Measure → Measure → Set) : Set₁ where
  constructor strictProgressRelation
  field
    isTransitive :
      ∀ {a b c} →
      a < b →
      b < c →
      a < c
    isIrreflexive :
      ∀ a → ¬ (a < a)

strictProgressRelation-from-witness :
  ∀ {State Measure : Set}
  {step : State → State}
  {_<_ : Measure → Measure → Set}
  (W : StrictProgressWitness State Measure step _<_) →
  StrictProgressRelation Measure _<_
strictProgressRelation-from-witness W =
  strictProgressRelation
    (StrictProgressWitness.strictProgressTransitive W)
    (StrictProgressWitness.strictProgressIrreflexive W)

strictProgressWitness-from-relation :
  ∀ {State Measure : Set}
  {step : State → State}
  {_<_ : Measure → Measure → Set}
  (R : StrictProgressRelation Measure _<_)
  (measure : State → Measure)
  (stepProgress :
    ∀ s → measure s < measure (step s)) →
  StrictProgressWitness State Measure step _<_
strictProgressWitness-from-relation R measure stepProgress =
  strictProgressWitness
    measure
    stepProgress
    (StrictProgressRelation.isTransitive R)
    (StrictProgressRelation.isIrreflexive R)

open StrictProgressWitness public

strictProgressAfterIterate :
  ∀ {State Measure : Set}
  {step : State → State}
  {_<_ : Measure → Measure → Set}
  (W : StrictProgressWitness State Measure step _<_)
  (n : ℕ)
  (s : State) →
  measure W s <
  measure W (iterateStep step (succ n) s)
strictProgressAfterIterate W zero s =
  stepProgress W s
strictProgressAfterIterate W (succ n) s =
  StrictProgressWitness.strictProgressTransitive W
    (stepProgress W s)
    (strictProgressAfterIterate W n (step s))

noPositiveFiniteCycleFromStrictProgress :
  ∀ {State Measure : Set}
  {step : State → State}
  {_<_ : Measure → Measure → Set}
  (W : StrictProgressWitness State Measure step _<_)
  (n : ℕ)
  (s : State) →
  iterateStep step (succ n) s ＝ s →
  ⊥
noPositiveFiniteCycleFromStrictProgress W n s eq =
  StrictProgressWitness.strictProgressIrreflexive W
    (measure W s)
    (transport (λ t → measure W s < measure W t)
      eq
      (strictProgressAfterIterate W n s))


record NatSuccessorProgressWitness
  (State : Set)
  (step : State → State)
  (measure : State → ℕ) : Set₁ where
  constructor natSuccessorProgressWitness
  field
    successor :
      ∀ s →
      measure (step s) ＝ succ (measure s)

open NatSuccessorProgressWitness public

sucInjective :
  ∀ {m n : ℕ} → succ m ＝ succ n → m ＝ n
sucInjective refl = refl

natPlusLeftCancel :
  ∀ (k m n : ℕ) → k + m ＝ k + n → m ＝ n
natPlusLeftCancel zero m n eq = eq
natPlusLeftCancel (succ k) m n eq =
  natPlusLeftCancel k m n (sucInjective eq)

successorMeasureAfterIterate :
  ∀ {State : Set}
  {step : State → State}
  {measure : State → ℕ}
  (W : NatSuccessorProgressWitness State step measure)
  (n : ℕ)
  (s : State) →
  measure (iterateStep step n s) ＝ measure s + n
successorMeasureAfterIterate W zero s =
  sym (zero-right-neutral (measure W s))
successorMeasureAfterIterate W (succ n) s =
  trans
    (successor W (iterateStep (step W) n s))
    (trans
      (ap succ (successorMeasureAfterIterate W n s))
      (sym (succ-right (measure W s) n)))

successorMeasureOrbitInjective :
  ∀ {State : Set}
  {step : State → State}
  {measure : State → ℕ}
  (W : NatSuccessorProgressWitness State step measure)
  (s : State)
  {m n : ℕ} →
  iterateStep step m s ＝ iterateStep step n s →
  m ＝ n
successorMeasureOrbitInjective W s {m} {n} eq =
  natPlusLeftCancel
    (measure W s)
    m
    n
    (trans
      (sym (successorMeasureAfterIterate W m s))
      (trans
        (ap (measure W) eq)
        (successorMeasureAfterIterate W n s)))

natSucProgress : ∀ n → n < succ n
natSucProgress n = ≤-refl (succ n)

canonicalTotalCountStepProgress :
  ∀ {A : Set}
  (K : C.FullLearnerKernel A)
  (s : C.FullLearnerState A) →
  C.totalCount (C.lcbCounts s) <
  C.totalCount (C.lcbCounts (C.canonicalFullStep K s))
canonicalTotalCountStepProgress K s =
  transport (λ t → C.totalCount (C.lcbCounts s) < t)
    (C.canonicalTotalCountStep K s)
    (natSucProgress (C.totalCount (C.lcbCounts s)))

canonicalTotalCountStrictProgress :
  ∀ {A : Set}
  (K : C.FullLearnerKernel A) →
  StrictProgressWitness
    (C.FullLearnerState A)
    ℕ
    (C.canonicalFullStep K)
    _<_
canonicalTotalCountStrictProgress K =
  strictProgressWitness
    (λ s → C.totalCount (C.lcbCounts s))
    (λ s → canonicalTotalCountStepProgress K s)
    <-trans
    (λ n → megaNatNoStrictBack {n = n})

canonicalNoPositiveCycleFromTotalCount :
  ∀ {A : Set}
  (K : C.FullLearnerKernel A)
  (n : ℕ)
  (s : C.FullLearnerState A) →
  iterateStep (C.canonicalFullStep K) (succ n) s ＝ s →
  ⊥
canonicalNoPositiveCycleFromTotalCount K n s =
  noPositiveFiniteCycleFromStrictProgress
    (canonicalTotalCountStrictProgress K)
    n
    s


------------------------------------------------------------------------
-- 2026-09-26 theorem-improvement closure layer.
--
-- These interfaces deliberately remain in the theorem monolith and use
-- only the imports already present above. Each bridge is proof-relevant:
-- no graph edge, semantic label, convergence claim, or economic claim is
-- promoted without an explicit inhabitant.
------------------------------------------------------------------------

record MonolithStrictProgressClosure
  (State Measure : Set)
  (step : State → State)
  (_<_ : Measure → Measure → Set) : Set₁ where
  constructor monolithStrictProgressClosure
  field
    witness :
      StrictProgressWitness State Measure step _<_
    noPositiveCycle :
      ∀ n s →
      iterateStep step (succ n) s ＝ s →
      ⊥

open MonolithStrictProgressClosure public

monolithStrictProgressClosure-from-witness :
  ∀ {State Measure : Set}
  {step : State → State}
  {_<_ : Measure → Measure → Set}
  (W : StrictProgressWitness State Measure step _<_) →
  MonolithStrictProgressClosure State Measure step _<_
monolithStrictProgressClosure-from-witness W =
  monolithStrictProgressClosure
    W
    (λ n s →
      noPositiveFiniteCycleFromStrictProgress W n s)

canonicalTotalCountStrictProgress-closure :
  ∀ {A : Set}
  (K : C.FullLearnerKernel A) →
  MonolithStrictProgressClosure
    (C.FullLearnerState A)
    ℕ
    (C.canonicalFullStep K)
    _<_
canonicalTotalCountStrictProgress-closure K =
  monolithStrictProgressClosure-from-witness
    (canonicalTotalCountStrictProgress K)

record MonolithFactorTransitionClosure
  (State Factor : Set)
  (step : State → State)
  (related : State → State → Set)
  (observe : State → Factor) : Set₁ where
  constructor monolithFactorTransitionClosure
  field
    factorStep : Factor → Factor
    factorStepCommutes :
      ∀ s →
      observe (step s) ＝ factorStep (observe s)
    observeRespects :
      ∀ {s t} →
      related s t →
      observe s ＝ observe t
    relationStepPreserved :
      ∀ {s t} →
      related s t →
      related (step s) (step t)

monolithFactorTransition-to-relationWitness :
  ∀ {State Factor : Set}
  {step : State → State}
  {related : State → State → Set}
  {observe : State → Factor}
  (W : MonolithFactorTransitionClosure
    State
    Factor
    step
    related
    observe) →
  RelationFactorTransitionWitness
    State
    Factor
    step
    related
    observe
monolithFactorTransition-to-relationWitness W =
  relationFactorTransitionWitness
    (factorTransitionWitness
      (MonolithFactorTransitionClosure.factorStep W)
      (MonolithFactorTransitionClosure.factorStepCommutes W))
    (MonolithFactorTransitionClosure.observeRespects W)
    (MonolithFactorTransitionClosure.relationStepPreserved W)

record MonolithCommutingSquareTransport
  (A B : Set)
  (sourceStep : A → A)
  (targetStep : B → B) : Set₁ where
  constructor monolithCommutingSquareTransport
  field
    square :
      StepConjugacyWitness A B sourceStep targetStep

monolithCommutingSquare-iterate :
  ∀ {A B : Set}
  {sourceStep : A → A}
  {targetStep : B → B}
  (W : MonolithCommutingSquareTransport
    A B
    sourceStep
    targetStep)
  (n : ℕ)
  (a : A) →
  to (isomorphism (square W))
    (iterateIsomorphism sourceStep n a)
  ＝
  iterateIsomorphism targetStep n
    (to (isomorphism (square W)) a)
monolithCommutingSquare-iterate W =
  stepConjugacy-iterate (square W)

monolithCommutingSquare-property :
  ∀ {A B : Set}
  {sourceStep : A → A}
  {targetStep : B → B}
  (W : MonolithCommutingSquareTransport
    A B
    sourceStep
    targetStep)
  (P : A → Set)
  (Q : B → Set)
  (bridge :
    ∀ a →
    P a →
    Q (to (isomorphism (square W)) a))
  (preserved :
    ∀ b →
    Q b →
    Q (targetStep b)) →
  ∀ n a →
  P a →
  Q
    (iterateIsomorphism targetStep n
      (to (isomorphism (square W)) a))
monolithCommutingSquare-property W P Q bridge preserved =
  stepConjugacy-property-transport
    (square W)
    P
    Q
    bridge
    preserved

record MonolithProductionSideAssumptionBundle
  (Agent Firm Price Consumption ProductionPlan Allocation : Set)
  (consumer : Agent → Consumption)
  (production : Firm → ProductionPlan)
  (price : Price)
  (allocation : Allocation)
  (consumerOptimal : Agent → Consumption → Set)
  (productionFeasible : Firm → ProductionPlan → Set)
  (firmOptimal : Firm → Price → ProductionPlan → Set)
  (consumptionFeasible : Agent → Consumption → Set)
  (aggregateFeasible : Allocation → Set)
  (marketClearing : Price → Allocation → Set)
  (supportingPrice : Price → Allocation → Set) : Set₁ where
  constructor monolithProductionSideAssumptionBundle
  field
    consumerOptimality :
      ∀ i →
      consumerOptimal i (consumer i)
    productionFeasibility :
      ∀ j →
      productionFeasible j (production j)
    firmProfitOptimality :
      ∀ j →
      firmOptimal j price (production j)
    consumptionFeasibility :
      ∀ i →
      consumptionFeasible i (consumer i)
    aggregateFeasibility :
      aggregateFeasible allocation
    bundleMarketClearingWitness :
      marketClearing price allocation
    bundleSupportingPriceWitness :
      supportingPrice price allocation

open MonolithProductionSideAssumptionBundle public

------------------------------------------------------------------------
-- Expanded generalized aggregate-excess-demand e-graph seam.
--
-- This layer separates individual demand/supply, aggregation, excess
-- demand, regularity, market clearing, supporting prices, and equilibrium
-- characterization. None of these edges is inferred from a label alone.
-- Continuity, degree-zero homogeneity, and Walras' law are explicit
-- requirements; they are not consequences of representation injectivity.
------------------------------------------------------------------------

record GeneralizedIndividualDemandWitness
  (Agent Price Consumption : Set)
  (demand : Price → Agent → Consumption)
  (optimal : Price → Agent → Consumption → Set) : Set₁ where
  constructor generalizedIndividualDemandWitness
  field
    demandOptimal :
      ∀ p i →
      optimal p i (demand p i)

record GeneralizedFirmSupplyWitness
  (Firm Price ProductionPlan : Set)
  (supply : Price → Firm → ProductionPlan)
  (optimal : Firm → Price → ProductionPlan → Set) : Set₁ where
  constructor generalizedFirmSupplyWitness
  field
    supplyOptimal :
      ∀ p j →
      optimal j p (supply p j)

record GeneralizedAggregateDemandSupplyWitness
  (Agent Firm Price Consumption ProductionPlan Allocation : Set)
  (demand : Price → Agent → Consumption)
  (supply : Price → Firm → ProductionPlan)
  (aggregateDemand : (Agent → Consumption) → Allocation)
  (aggregateSupply : (Firm → ProductionPlan) → Allocation) : Set₁ where
  constructor generalizedAggregateDemandSupplyWitness
  field
    aggregateDemandAt :
      Price → Allocation
    aggregateSupplyAt :
      Price → Allocation
    aggregateDemandDefinition :
      ∀ p →
      aggregateDemandAt p ＝
      aggregateDemand (λ i → demand p i)
    aggregateSupplyDefinition :
      ∀ p →
      aggregateSupplyAt p ＝
      aggregateSupply (λ j → supply p j)

record GeneralizedAggregateExcessDemandWitness
  (Price Allocation ExcessDemand : Set)
  (aggregateDemandAt aggregateSupplyAt : Price → Allocation)
  (subtract : Allocation → Allocation → ExcessDemand)
  (excessDemand : Price → ExcessDemand) : Set₁ where
  constructor generalizedAggregateExcessDemandWitness
  field
    excessDefinition :
      ∀ p →
      excessDemand p ＝
      subtract
        (aggregateDemandAt p)
        (aggregateSupplyAt p)

record GeneralizedAggregateExcessDemandRegularityWitness
  (Price ExcessDemand : Set)
  (excessDemand : Price → ExcessDemand)
  (continuous homogeneousZero walrasLaw :
    (Price → ExcessDemand) → Set) : Set₁ where
  constructor generalizedAggregateExcessDemandRegularityWitness
  field
    continuity :
      continuous excessDemand
    homogeneity :
      homogeneousZero excessDemand
    walras :
      walrasLaw excessDemand

record GeneralizedAggregateMarketClearingWitness
  (Price ExcessDemand : Set)
  (excessDemand : Price → ExcessDemand)
  (zeroExcess : ExcessDemand)
  (marketClearing : Price → Set) : Set₁ where
  constructor generalizedAggregateMarketClearingWitness
  field
    clearingFromZero :
      ∀ p →
      excessDemand p ＝ zeroExcess →
      marketClearing p

record GeneralizedAggregateSupportingPriceWitness
  (Price Allocation ExcessDemand : Set)
  (aggregateAllocation : Price → Allocation)
  (excessDemand : Price → ExcessDemand)
  (zeroExcess : ExcessDemand)
  (supports : Price → Allocation → Set) : Set₁ where
  constructor generalizedAggregateSupportingPriceWitness
  field
    supportingFromZero :
      ∀ p →
      excessDemand p ＝ zeroExcess →
      supports p (aggregateAllocation p)

record ExpandedGeneralizedAggregateExcessDemandKernel
  (Agent Firm Price Consumption ProductionPlan Allocation ExcessDemand : Set)
  (demand : Price → Agent → Consumption)
  (supply : Price → Firm → ProductionPlan)
  (aggregateDemand : (Agent → Consumption) → Allocation)
  (aggregateSupply : (Firm → ProductionPlan) → Allocation)
  (aggregateDemandAt aggregateSupplyAt : Price → Allocation)
  (subtract : Allocation → Allocation → ExcessDemand)
  (excessDemand : Price → ExcessDemand)
  (zeroExcess : ExcessDemand)
  (optimalDemand : Price → Agent → Consumption → Set)
  (optimalSupply : Firm → Price → ProductionPlan → Set)
  (continuous homogeneousZero walrasLaw :
    (Price → ExcessDemand) → Set)
  (aggregateFeasible : Price → Allocation → Set)
  (marketClearing : Price → Set)
  (supports : Price → Allocation → Set)
  (equilibrium : Price → Allocation → Set) : Set₁ where
  constructor expandedGeneralizedAggregateExcessDemandKernel
  field
    demandWitness :
      GeneralizedIndividualDemandWitness
        Agent
        Price
        Consumption
        demand
        optimalDemand
    supplyWitness :
      GeneralizedFirmSupplyWitness
        Firm
        Price
        ProductionPlan
        supply
        optimalSupply
    aggregateDemandSupplyWitness :
      GeneralizedAggregateDemandSupplyWitness
        Agent
        Firm
        Price
        Consumption
        ProductionPlan
        Allocation
        demand
        supply
        aggregateDemand
        aggregateSupply
    aggregateDemandSupplyAt :
      ∀ p →
      aggregateDemandAt p ＝
      GeneralizedAggregateDemandSupplyWitness.aggregateDemandAt
        aggregateDemandSupplyWitness
        p
    aggregateSupplySupplyAt :
      ∀ p →
      aggregateSupplyAt p ＝
      GeneralizedAggregateDemandSupplyWitness.aggregateSupplyAt
        aggregateDemandSupplyWitness
        p
    generalizedAggregateFeasibilityAt :
      ∀ p →
      aggregateFeasible p (aggregateDemandAt p)
    excessWitness :
      GeneralizedAggregateExcessDemandWitness
        Price
        Allocation
        ExcessDemand
        aggregateDemandAt
        aggregateSupplyAt
        subtract
        excessDemand
    regularityWitness :
      GeneralizedAggregateExcessDemandRegularityWitness
        Price
        ExcessDemand
        excessDemand
        continuous
        homogeneousZero
        walrasLaw
    generalizedMarketClearingWitness :
      GeneralizedAggregateMarketClearingWitness
        Price
        ExcessDemand
        excessDemand
        zeroExcess
        marketClearing
    generalizedSupportingPriceWitness :
      GeneralizedAggregateSupportingPriceWitness
        Price
        Allocation
        ExcessDemand
        aggregateDemandAt
        excessDemand
        zeroExcess
        supports
    equilibriumCharacterization :
      ∀ p →
      excessDemand p ＝ zeroExcess →
      equilibrium p (aggregateDemandAt p)

expandedGeneralizedAggregateExcessDemand-closure :
  ∀ {Agent Firm Price Consumption ProductionPlan Allocation ExcessDemand : Set}
  {demand : Price → Agent → Consumption}
  {supply : Price → Firm → ProductionPlan}
  {aggregateDemand : (Agent → Consumption) → Allocation}
  {aggregateSupply : (Firm → ProductionPlan) → Allocation}
  {aggregateDemandAt aggregateSupplyAt : Price → Allocation}
  {subtract : Allocation → Allocation → ExcessDemand}
  {excessDemand : Price → ExcessDemand}
  {zeroExcess : ExcessDemand}
  {optimalDemand : Price → Agent → Consumption → Set}
  {optimalSupply : Firm → Price → ProductionPlan → Set}
  {continuous homogeneousZero walrasLaw :
    (Price → ExcessDemand) → Set}
  {aggregateFeasible : Price → Allocation → Set}
  {marketClearing : Price → Set}
  {supports : Price → Allocation → Set}
  {equilibrium : Price → Allocation → Set}
  (W :
    ExpandedGeneralizedAggregateExcessDemandKernel
      Agent
      Firm
      Price
      Consumption
      ProductionPlan
      Allocation
      ExcessDemand
      demand
      supply
      aggregateDemand
      aggregateSupply
      aggregateDemandAt
      aggregateSupplyAt
      subtract
      excessDemand
      zeroExcess
      optimalDemand
      optimalSupply
      continuous
      homogeneousZero
      walrasLaw
      aggregateFeasible
      marketClearing
      supports
      equilibrium) →
  ∀ p →
  excessDemand p ＝ zeroExcess →
  aggregateFeasible p (aggregateDemandAt p) ×
  marketClearing p ×
  supports p (aggregateDemandAt p) ×
  equilibrium p (aggregateDemandAt p)
expandedGeneralizedAggregateExcessDemand-closure W p root =
  ( ExpandedGeneralizedAggregateExcessDemandKernel.generalizedAggregateFeasibilityAt W p
  , GeneralizedAggregateMarketClearingWitness.clearingFromZero
      (ExpandedGeneralizedAggregateExcessDemandKernel.generalizedMarketClearingWitness W) p root
  , GeneralizedAggregateSupportingPriceWitness.supportingFromZero
      (ExpandedGeneralizedAggregateExcessDemandKernel.generalizedSupportingPriceWitness W) p root
  , ExpandedGeneralizedAggregateExcessDemandKernel.equilibriumCharacterization W p root )

------------------------------------------------------------------------
-- E-graph composition node: semantic path plus the entire economic
-- demand -> supply -> aggregate -> excess -> root -> closure chain.
-- Convergence remains a separate witness and is not manufactured here.
------------------------------------------------------------------------

record EGraphEconomicAggregateExcessDemandComposition
  (Expression State Agent Firm Price Consumption ProductionPlan Allocation ExcessDemand : Set)
  (R :
    EGraphSemanticInterpretation
      Expression
      State)
  (e f : Expression)
  (demand : Price → Agent → Consumption)
  (supply : Price → Firm → ProductionPlan)
  (aggregateDemand : (Agent → Consumption) → Allocation)
  (aggregateSupply : (Firm → ProductionPlan) → Allocation)
  (aggregateDemandAt aggregateSupplyAt : Price → Allocation)
  (subtract : Allocation → Allocation → ExcessDemand)
  (excessDemand : Price → ExcessDemand)
  (zeroExcess : ExcessDemand)
  (optimalDemand : Price → Agent → Consumption → Set)
  (optimalSupply : Firm → Price → ProductionPlan → Set)
  (continuous homogeneousZero walrasLaw :
    (Price → ExcessDemand) → Set)
  (aggregateFeasible : Price → Allocation → Set)
  (marketClearing : Price → Set)
  (supports : Price → Allocation → Set)
  (equilibrium : Price → Allocation → Set) : Set₁ where
  constructor eGraphEconomicAggregateExcessDemandComposition
  field
    semanticPath :
      EGraphSemanticPath R e f
    economicKernel :
      ExpandedGeneralizedAggregateExcessDemandKernel
        Agent
        Firm
        Price
        Consumption
        ProductionPlan
        Allocation
        ExcessDemand
        demand
        supply
        aggregateDemand
        aggregateSupply
        aggregateDemandAt
        aggregateSupplyAt
        subtract
        excessDemand
        zeroExcess
        optimalDemand
        optimalSupply
        continuous
        homogeneousZero
        walrasLaw
        aggregateFeasible
        marketClearing
        supports
        equilibrium

eGraphEconomicAggregateExcessDemand-closure :
  ∀ {Expression State Agent Firm Price Consumption ProductionPlan Allocation ExcessDemand : Set}
  {R :
    EGraphSemanticInterpretation
      Expression
      State}
  {e f : Expression}
  {demand : Price → Agent → Consumption}
  {supply : Price → Firm → ProductionPlan}
  {aggregateDemand : (Agent → Consumption) → Allocation}
  {aggregateSupply : (Firm → ProductionPlan) → Allocation}
  {aggregateDemandAt aggregateSupplyAt : Price → Allocation}
  {subtract : Allocation → Allocation → ExcessDemand}
  {excessDemand : Price → ExcessDemand}
  {zeroExcess : ExcessDemand}
  {optimalDemand : Price → Agent → Consumption → Set}
  {optimalSupply : Firm → Price → ProductionPlan → Set}
  {continuous homogeneousZero walrasLaw :
    (Price → ExcessDemand) → Set}
  {aggregateFeasible : Price → Allocation → Set}
  {marketClearing : Price → Set}
  {supports : Price → Allocation → Set}
  {equilibrium : Price → Allocation → Set}
  (W :
    EGraphEconomicAggregateExcessDemandComposition
      Expression
      State
      Agent
      Firm
      Price
      Consumption
      ProductionPlan
      Allocation
      ExcessDemand
      R
      e
      f
      demand
      supply
      aggregateDemand
      aggregateSupply
      aggregateDemandAt
      aggregateSupplyAt
      subtract
      excessDemand
      zeroExcess
      optimalDemand
      optimalSupply
      continuous
      homogeneousZero
      walrasLaw
      aggregateFeasible
      marketClearing
      supports
      equilibrium) →
  EGraphSemanticPath R e f ×
  (∀ p →
    excessDemand p ＝ zeroExcess →
    aggregateFeasible p (aggregateDemandAt p) ×
    marketClearing p ×
    supports p (aggregateDemandAt p) ×
    equilibrium p (aggregateDemandAt p))
eGraphEconomicAggregateExcessDemand-closure W =
  EGraphEconomicAggregateExcessDemandComposition.semanticPath W
  , expandedGeneralizedAggregateExcessDemand-closure
      (EGraphEconomicAggregateExcessDemandComposition.economicKernel W)

------------------------------------------------------------------------
-- Research note: this node records the literature-facing requirements.
-- It does not turn continuity/homogeneity/Walras law into an existence
-- theorem, and it does not turn a root witness into convergence.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Root-to-fixed-point transport is an explicit economic edge.
--
-- The update operator and its root-to-fixed-point law are supplied as
-- mathematical structure. The resulting edge is a direct Agda
-- implication from an excess-demand root to a fixed point.
------------------------------------------------------------------------

record GeneralizedAggregateExcessDemandFixedPointWitness
  (Price ExcessDemand : Set)
  (excessDemand : Price → ExcessDemand)
  (zeroExcess : ExcessDemand)
  (priceUpdate : Price → Price) : Set₁ where
  constructor generalizedAggregateExcessDemandFixedPointWitness
  field
    fixedPointFromRoot :
      ∀ p →
      excessDemand p ＝ zeroExcess →
      priceUpdate p ＝ p

expandedGeneralizedAggregateExcessDemand-fixedPoint :
  ∀ {Price ExcessDemand : Set}
  {excessDemand : Price → ExcessDemand}
  {zeroExcess : ExcessDemand}
  {priceUpdate : Price → Price}
  (W :
    GeneralizedAggregateExcessDemandFixedPointWitness
      Price
      ExcessDemand
      zeroExcess
      priceUpdate) →
  ∀ p →
  excessDemand p ＝ zeroExcess →
  priceUpdate p ＝ p
expandedGeneralizedAggregateExcessDemand-fixedPoint W p root =
  GeneralizedAggregateExcessDemandFixedPointWitness.fixedPointFromRoot W p root

record EGraphEconomicAggregateExcessDemandFixedPointComposition
  (Expression State Price ExcessDemand : Set)
  (R :
    EGraphSemanticInterpretation
      Expression
      State)
  (e f : Expression)
  (excessDemand : Price → ExcessDemand)
  (zeroExcess : ExcessDemand)
  (priceUpdate : Price → Price) : Set₁ where
  constructor eGraphEconomicAggregateExcessDemandFixedPointComposition
  field
    semanticPath :
      EGraphSemanticPath R e f
    fixedPointWitness :
      GeneralizedAggregateExcessDemandFixedPointWitness
        Price
        ExcessDemand
        excessDemand
        zeroExcess
        priceUpdate

eGraphEconomicAggregateExcessDemand-fixedPointClosure :
  ∀ {Expression State Price ExcessDemand : Set}
  {R :
    EGraphSemanticInterpretation
      Expression
      State}
  {e f : Expression}
  {excessDemand : Price → ExcessDemand}
  {zeroExcess : ExcessDemand}
  {priceUpdate : Price → Price}
  (W :
    EGraphEconomicAggregateExcessDemandFixedPointComposition
      Expression
      State
      Price
      ExcessDemand
      R
      e
      f
      excessDemand
      zeroExcess
      priceUpdate) →
  EGraphSemanticPath R e f ×
  (∀ p →
    excessDemand p ＝ zeroExcess →
    priceUpdate p ＝ p)
eGraphEconomicAggregateExcessDemand-fixedPointClosure W =
  EGraphEconomicAggregateExcessDemandFixedPointComposition.semanticPath W
  , expandedGeneralizedAggregateExcessDemand-fixedPoint
      (EGraphEconomicAggregateExcessDemandFixedPointComposition.fixedPointWitness W)

------------------------------------------------------------------------
-- The production/economic bridge now has an explicit fixed-point seam.
-- No convergence theorem is inferred from a fixed point.
------------------------------------------------------------------------

record MonolithStationaryLawBridge
  (Distribution Economic : Set)
  (P : Distribution → Distribution)
  (μ : ℕ → Distribution)
  (μ∞ : Distribution)
  (Converges : (ℕ → Distribution) → Distribution → Set)
  (aggregate : Distribution → Economic)
  (economicStep : Economic → Economic) : Set₁ where
  constructor monolithStationaryLawBridge
  field
    distributionalLimit :
      StationaryLimitTheorem
        Distribution
        P
        μ
        μ∞
        Converges
    aggregateCommutes :
      ∀ d →
      aggregate (P d) ＝ economicStep (aggregate d)

monolithStationaryLawBridge-stationary :
  ∀ {Distribution Economic : Set}
  {P : Distribution → Distribution}
  {μ : ℕ → Distribution}
  {μ∞ : Distribution}
  {Converges : (ℕ → Distribution) → Distribution → Set}
  {aggregate : Distribution → Economic}
  {economicStep : Economic → Economic}
  (W :
    MonolithStationaryLawBridge
      Distribution
      Economic
      P
      μ
      μ∞
      Converges
      aggregate
      economicStep) →
  economicStep (aggregate μ∞) ＝ aggregate μ∞
monolithStationaryLawBridge-stationary W =
  distributionalStationaryAggregate-stationary
    (distributionalStationaryAggregateTransport
      (MonolithStationaryLawBridge.distributionalLimit W)
      (MonolithStationaryLawBridge.aggregateCommutes W))

record MonolithEGraphProofCertificate
  (Node Edge Assumption : Set) : Set₁ where
  constructor monolithEGraphProofCertificate
  field
    source : Edge → Node
    target : Edge → Node
    semanticAssumption : Edge → Assumption
    proofWitness : Edge → Set
    proofSound :
      ∀ e →
      proofWitness e
    assumptionToProof :
      ∀ e →
      semanticAssumption e → proofWitness e

record MonolithEGraphClosureCertificate
  (Node Edge Assumption : Set) : Set₁ where
  constructor monolithEGraphClosureCertificate
  field
    certificate :
      MonolithEGraphProofCertificate
        Node
        Edge
        Assumption
    closedEdge :
      Edge → Set

monolithEGraphClosureCertificate-from-proof :
  ∀ {Node Edge Assumption : Set}
  (W :
    MonolithEGraphProofCertificate
      Node
      Edge
      Assumption) →
  MonolithEGraphClosureCertificate
    Node
    Edge
    Assumption
monolithEGraphClosureCertificate-from-proof W =
  monolithEGraphClosureCertificate
    W
    (λ e → MonolithEGraphProofCertificate.proofWitness W e)


------------------------------------------------------------------------
-- Unconditional finite-candidate price kernel.
--
-- This is deliberately weaker than a Walrasian existence theorem:
-- for any finite candidate-price list and an explicit decision procedure
-- for the supporting relation at the chosen allocation, the kernel
-- unconditionally returns either a supporting-price witness or a complete
-- rejection certificate for the supplied candidate list.
--
-- No new imports are required. The result does not claim that a supporting
-- price exists outside the supplied finite candidate set.
------------------------------------------------------------------------

data FiniteCandidateDecision (P : Set) : Set where
  acceptCandidate : P → FiniteCandidateDecision P
  rejectCandidate : (P → ⊥) → FiniteCandidateDecision P

FiniteCandidatePriceResult :
  (Price Allocation : Set) →
  (supports : Price → Allocation → Set) →
  Allocation →
  Set₁
FiniteCandidatePriceResult Price Allocation supports allocation =
  (Σ Price (λ p → supports p allocation))
  ⊎
  List (Σ Price (λ p → supports p allocation → ⊥))

finiteCandidatePriceSearch :
  ∀ {Price Allocation : Set}
  (supports : Price → Allocation → Set)
  (allocation : Allocation)
  (decide : ∀ p → FiniteCandidateDecision (supports p allocation))
  (candidates : List Price) →
  FiniteCandidatePriceResult Price Allocation supports allocation
finiteCandidatePriceSearch supports allocation decide [] =
  inj₂ []
finiteCandidatePriceSearch supports allocation decide (p ∷ ps) with decide p
... | acceptCandidate witness =
  inj₁ (p , witness)
... | rejectCandidate refute with
  finiteCandidatePriceSearch supports allocation decide ps
...   | inj₁ witness =
  inj₁ witness
...   | inj₂ rejected =
  inj₂ ((p , refute) ∷ rejected)

finiteCandidatePriceSearch-complete :
  ∀ {Price Allocation : Set}
  (supports : Price → Allocation → Set)
  (allocation : Allocation)
  (decide : ∀ p → FiniteCandidateDecision (supports p allocation))
  (candidates : List Price) →
  FiniteCandidatePriceResult Price Allocation supports allocation
finiteCandidatePriceSearch-complete =
  finiteCandidatePriceSearch


------------------------------------------------------------------------
-- Unconditional tragedy-of-the-commons non-derivability.
--
-- This boundary is deliberately more primitive than price or equilibrium.
-- It separates individual local optimality from preservation of a shared
-- resource, and the concrete countermodel makes the depletion mechanism
-- explicit: two agents each choose the individually optimal one-unit
-- extraction while the common stock has capacity one.
------------------------------------------------------------------------

record CommonsPreservationDerivation
  (World Agent Action Resource : Set)
  (sharedResource : World → Resource)
  (resourceCapacity : Resource → ℕ)
  (action : World → Agent → Action)
  (extraction : Action → ℕ)
  (aggregateExtraction : World → ℕ)
  (localOptimal : World → Agent → Action → Set) : Set₁ where
  constructor commonsPreservationDerivation
  field
    derive :
      ∀ w →
      (∀ a → localOptimal w a (action w a)) →
      aggregateExtraction w ≤
      resourceCapacity (sharedResource w)

open CommonsPreservationDerivation public

record CommonsNonDerivabilityCounterexample : Set₁ where
  constructor commonsNonDerivabilityCounterexample
  field
    World : Set
    Agent : Set
    Action : Set
    Resource : Set
    sharedResource : World → Resource
    resourceCapacity : Resource → ℕ
    action : World → Agent → Action
    extraction : Action → ℕ
    aggregateExtraction : World → ℕ
    localOptimal : World → Agent → Action → Set
    commonsWorld : World
    commonResource :
      sharedResource commonsWorld
    allLocallyOptimal :
      ∀ a →
      localOptimal
        commonsWorld
        a
        (action commonsWorld a)
    aggregateExtractionIsTwo :
      aggregateExtraction commonsWorld ＝
      succ (succ zero)
    extractionIsOne :
      ∀ a →
      extraction (action commonsWorld a) ＝
      succ zero
    capacityIsOne :
      resourceCapacity (sharedResource commonsWorld) ＝
      succ zero

open CommonsNonDerivabilityCounterexample public

twoNotLeOne :
  ¬ succ (succ zero) ≤ succ zero
twoNotLeOne ()
noUnconditionalCommonsPreservation :
  ∀ (C : CommonsNonDerivabilityCounterexample) →
  ¬ CommonsPreservationDerivation
      (World C)
      (Agent C)
      (Action C)
      (Resource C)
      (sharedResource C)
      (resourceCapacity C)
      (action C)
      (extraction C)
      (aggregateExtraction C)
      (localOptimal C)
noUnconditionalCommonsPreservation C D =
  twoNotLeOne
    (transport (λ n → n ≤ succ zero)
      (capacityIsOne C)
      (transport (λ n → succ (succ zero) ≤ n)
        (aggregateExtractionIsTwo C)
        (derive D
          (commonsWorld C)
          (allLocallyOptimal C))))


twoAgentCommonsCounterexample :
  CommonsNonDerivabilityCounterexample
twoAgentCommonsCounterexample =
  commonsNonDerivabilityCounterexample
    (⊤)
    (⊤ ⊎ ⊤)
    (⊤ ⊎ ⊤)
    ℕ
    (λ _ → succ zero)
    (λ _ → succ zero)
    (λ _ _ → inj₂ tt)
    (λ _ → succ zero)
    (λ _ → succ (succ zero))
    (λ _ _ a → a ＝ inj₂ tt)
    tt
    refl
    (λ _ → refl)
    (λ _ → refl)
    (λ _ → refl)

noUnconditionalCommonsPreservation-twoAgent :
  ¬ CommonsPreservationDerivation
      (World twoAgentCommonsCounterexample)
      (Agent twoAgentCommonsCounterexample)
      (Action twoAgentCommonsCounterexample)
      (Resource twoAgentCommonsCounterexample)
      (sharedResource twoAgentCommonsCounterexample)
      (resourceCapacity twoAgentCommonsCounterexample)
      (action twoAgentCommonsCounterexample)
      (extraction twoAgentCommonsCounterexample)
      (aggregateExtraction twoAgentCommonsCounterexample)
      (localOptimal twoAgentCommonsCounterexample)
noUnconditionalCommonsPreservation-twoAgent =
  noUnconditionalCommonsPreservation
    twoAgentCommonsCounterexample

------------------------------------------------------------------------
-- The concrete model has the intended tragedy mechanism:
--
--   two agents
--      + one-unit shared stock
--      + one-unit private extraction is individually optimal
--      -> two units aggregate extraction
--      -> preservation predicate (extraction <= stock) fails.
--
-- This is not a theorem that every commons collapses. It is an
-- impossibility theorem against the unconditional implication from
-- local optimality alone to aggregate preservation. A positive bridge
-- must add coupling information such as quotas/property rights,
-- internalized externalities, coordination, or a regeneration/conservation
-- invariant.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Unconditional canonical-price non-derivability.
--
-- This stronger boundary preserves equilibrium existence and universal
-- Pareto optimality of equilibria, while showing that a price cannot be
-- unconditionally reconstructed from price-forgetting observations when
-- observationally identical worlds require disjoint supporting prices.
------------------------------------------------------------------------

record CanonicalPriceDerivation
  (World Obs Price Allocation : Set)
  (observe : World → Obs)
  (supports : World → Price → Allocation → Set)
  (equilibrium : World → Price → Allocation → Set) : Set₁ where
  constructor canonicalPriceDerivation
  field
    derive : Obs → Price
    sound :
      ∀ w p a →
      equilibrium w p a →
      supports w (derive (observe w)) a

open CanonicalPriceDerivation public

record CanonicalPriceNonIdentifiabilityCounterexample : Set₁ where
  constructor canonicalPriceNonIdentifiabilityCounterexample
  field
    World : Set
    Obs : Set
    Price : Set
    Allocation : Set
    observe : World → Obs
    supports : World → Price → Allocation → Set
    equilibrium : World → Price → Allocation → Set
    paretoOptimal : Allocation → Set
    world₁ : World
    world₂ : World
    allocation₁ : Allocation
    allocation₂ : Allocation
    price₁ : Price
    price₂ : Price
    sameObservation :
      observe world₁ ＝ observe world₂
    equilibrium₁ :
      equilibrium world₁ price₁ allocation₁
    equilibrium₂ :
      equilibrium world₂ price₂ allocation₂
    allEquilibriaParetoOptimal :
      ∀ {w p a} →
      equilibrium w p a →
      paretoOptimal a
    noCommonSupportingPrice :
      ¬ Σ Price
        (λ p →
          supports world₁ p allocation₁ ×
          supports world₂ p allocation₂)
    distinctPrices :
      price₁ ≢ price₂

open CanonicalPriceNonIdentifiabilityCounterexample public

transportCanonicalPriceSupport :
  ∀ {World Price Allocation : Set}
  {supports : World → Price → Allocation → Set}
  {w : World} {p q : Price} {a : Allocation} →
  p ＝ q →
  supports w p a →
  supports w q a
transportCanonicalPriceSupport refl proof =
  proof

noUnconditionalCanonicalPriceDerivation :
  ∀ (C : CanonicalPriceNonIdentifiabilityCounterexample) →
  ¬ CanonicalPriceDerivation
      (World C)
      (Obs C)
      (Price C)
      (Allocation C)
      (observe C)
      (supports C)
      (equilibrium C)
noUnconditionalCanonicalPriceDerivation C D =
  noCommonSupportingPrice C
    (derive D (observe C (world₁ C))
     , sound D
         (world₁ C)
         (price₁ C)
         (allocation₁ C)
         (equilibrium₁ C)
     , transportCanonicalPriceSupport
         (sym
           (ap
             (derive D)
             (sameObservation C)))
         (sound D
           (world₂ C)
           (price₂ C)
           (allocation₂ C)
           (equilibrium₂ C)))

-- Disjoint sum constructors rule out a shared canonical price.
twoPriceDistinct : inj₁ tt ≢ inj₂ tt
twoPriceDistinct ()

twoWorldsNoCommonSupportingPrice :
  ¬ Σ (⊤ ⊎ ⊤)
    (λ p →
      (inj₁ tt ＝ p) ×
      (inj₂ tt ＝ p))
twoWorldsNoCommonSupportingPrice
  (p , (support₁ , support₂)) =
  (λ ())
    (trans support₁ (sym support₂))

twoWorldCanonicalPriceNonIdentifiabilityCounterexample :
  CanonicalPriceNonIdentifiabilityCounterexample
twoWorldCanonicalPriceNonIdentifiabilityCounterexample =
  canonicalPriceNonIdentifiabilityCounterexample
    (⊤ ⊎ ⊤)
    ⊤
    (⊤ ⊎ ⊤)
    ⊤
    (λ _ → tt)
    (λ world price _ → world ＝ price)
    (λ world price allocation → world ＝ price)
    (λ _ → ⊤)
    (inj₁ tt)
    (inj₂ tt)
    tt
    tt
    (inj₁ tt)
    (inj₂ tt)
    refl
    refl
    refl
    (λ { refl → tt })
    twoWorldsNoCommonSupportingPrice
    twoPriceDistinct

noUnconditionalCanonicalPriceDerivation-twoWorld :
  ¬ CanonicalPriceDerivation
      (World twoWorldCanonicalPriceNonIdentifiabilityCounterexample)
      (Obs twoWorldCanonicalPriceNonIdentifiabilityCounterexample)
      (Price twoWorldCanonicalPriceNonIdentifiabilityCounterexample)
      (Allocation twoWorldCanonicalPriceNonIdentifiabilityCounterexample)
      (observe twoWorldCanonicalPriceNonIdentifiabilityCounterexample)
      (supports twoWorldCanonicalPriceNonIdentifiabilityCounterexample)
      (equilibrium twoWorldCanonicalPriceNonIdentifiabilityCounterexample)
noUnconditionalCanonicalPriceDerivation-twoWorld =
  noUnconditionalCanonicalPriceDerivation
    twoWorldCanonicalPriceNonIdentifiabilityCounterexample

------------------------------------------------------------------------
-- Canonical Integer-GRU token encoding: global left inverse, injectivity,
-- and exact recurrent conjugacy.
--
-- CanonicalToken is the unbounded integer carrier Int and IntCode is an exact
-- Int wrapper. The decoder below is therefore global and total. This proves
-- global injectivity directly from the left-inverse law; no separate
-- separation axiom is required. Continuity is only asserted for the
-- repository's discrete topology, not an analytic topology.
------------------------------------------------------------------------

canonicalTokenDecode : C.IntCode → C.CanonicalToken
canonicalTokenDecode = C.intCodeValue

canonicalTokenDecode-encode :
  ∀ t → canonicalTokenDecode (C.canonicalTokenEncode t) ＝ t
canonicalTokenDecode-encode t = refl

record CanonicalIntegerGRUTokenEncodingLeftInverse : Set₁ where
  constructor canonicalIntegerGRUTokenEncodingLeftInverse
  field
    decodeEncode :
      ∀ t →
      canonicalTokenDecode (C.canonicalTokenEncode t) ＝ t

open CanonicalIntegerGRUTokenEncodingLeftInverse public

canonical-integer-gru-token-encoding-left-inverse :
  CanonicalIntegerGRUTokenEncodingLeftInverse
canonical-integer-gru-token-encoding-left-inverse =
  canonicalIntegerGRUTokenEncodingLeftInverse
    canonicalTokenDecode-encode

canonicalIntegerGRUTokenEncodingInjective :
  ∀ {s t : C.CanonicalToken} →
  C.canonicalTokenEncode s ＝ C.canonicalTokenEncode t →
  s ＝ t
canonicalIntegerGRUTokenEncodingInjective {s} {t} eq =
  trans
    (sym (decodeEncode canonical-integer-gru-token-encoding-left-inverse s))
    (trans
      (ap canonicalTokenDecode eq)
      (decodeEncode canonical-integer-gru-token-encoding-left-inverse t))

record CanonicalIntegerGRUGlobalConjugateTheorem : Set₁ where
  constructor canonicalIntegerGRUGlobalConjugateTheorem
  field
    encodingLeftInverse :
      CanonicalIntegerGRUTokenEncodingLeftInverse
    encodingInjective :
      ∀ {s t : C.CanonicalToken} →
      C.canonicalTokenEncode s ＝ C.canonicalTokenEncode t →
      s ＝ t
    recurrentConjugacy :
      CanonicalGlobalTokenEncodingConjugacyTheorem

open CanonicalIntegerGRUGlobalConjugateTheorem public

canonical-integer-gru-global-conjugate-theorem :
  CanonicalIntegerGRUGlobalConjugateTheorem
canonical-integer-gru-global-conjugate-theorem =
  canonicalIntegerGRUGlobalConjugateTheorem
    canonical-integer-gru-token-encoding-left-inverse
    canonicalIntegerGRUTokenEncodingInjective
    canonical-global-token-encoding-conjugacy


------------------------------------------------------------------------
-- Current canonical arbitrary-limit Integer-GRU composition boundary.
--
-- The generic limit kernel is explicit: this theorem composes the proved
-- global Integer-GRU representation with a surviving limit left inverse.
-- It does not manufacture a concrete analytic limit, convergence witness,
-- projection family, or decoder coherence.
------------------------------------------------------------------------

record CanonicalIntegerGRUFractalLimitCompositionTheorem
  (LimitObservation : Set)
  (limitEncode : C.CanonicalToken → LimitObservation) : Set₁ where
  constructor canonicalIntegerGRUFractalLimitCompositionTheorem
  field
    globalRepresentation :
      CanonicalIntegerGRUGlobalConjugateTheorem
    limitKernel :
      GRUFractalLimitCompositionKernel
        C.CanonicalToken
        C.IntCode
        LimitObservation
        limitEncode
    limitInjective :
      ∀ {s t : C.CanonicalToken} →
      limitEncode s ＝ limitEncode t →
      s ＝ t

open CanonicalIntegerGRUFractalLimitCompositionTheorem public

canonical-integer-gru-fractal-limit-composition :
  ∀ {LimitObservation : Set}
  {limitEncode : C.CanonicalToken → LimitObservation} →
  GRUFractalLimitCompositionKernel
    C.CanonicalToken
    C.IntCode
    LimitObservation
    limitEncode →
  CanonicalIntegerGRUFractalLimitCompositionTheorem
    LimitObservation
    limitEncode
canonical-integer-gru-fractal-limit-composition K =
  canonicalIntegerGRUFractalLimitCompositionTheorem
    canonical-integer-gru-global-conjugate-theorem
    K
    (gruFractalLimitComposition-limitInjective K)


------------------------------------------------------------------------
-- Inlined nested commons composition boundary; the one-level commons
-- theorem already lives in this monolith above.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Nested / self-similar commons composition boundary.
--
-- The construction is deliberately proposition-valued: no Bool is needed.
-- Each level repeats the same local-optimality -> aggregate-preservation
-- obligation. A global derivation must therefore solve the obligation at
-- every inhabited level. The existing two-agent countermodel refutes that
-- unconditional implication already at one level, and hence also refutes
-- the nested version.
------------------------------------------------------------------------


------------------------------------------------------------------------
-- A single commons law repeated across an arbitrary collection of levels.
-- "Nested" here is a precise recursive/self-similar interface claim:
-- the same preservation obligation is required independently at every
-- level.
------------------------------------------------------------------------

record NestedCommonsPreservationDerivation
  (Level : Set)
  (C : CommonsNonDerivabilityCounterexample) : Set₁ where
  constructor nestedCommonsPreservationDerivation
  field
    derive :
      ∀ level →
      ∀ w →
      (∀ a →
        localOptimal C
          w
          a
          (action C w a)) →
      aggregateExtraction C w ≤
      resourceCapacity C (sharedResource C w)

open NestedCommonsPreservationDerivation public

------------------------------------------------------------------------
-- Aggregate consistency for the concrete two-agent model.
-- This makes "two-unit aggregate extraction" mathematically tied to the
-- two individual one-unit extractions rather than merely co-present fields.
------------------------------------------------------------------------

twoAgentAggregateExtractionIsSum :
  aggregateExtraction twoAgentCommonsCounterexample
    (commonsWorld twoAgentCommonsCounterexample)
  ＝
  extraction twoAgentCommonsCounterexample
    (action twoAgentCommonsCounterexample
      (inj₁ tt))
  +
  extraction twoAgentCommonsCounterexample
    (action twoAgentCommonsCounterexample
      (inj₂ tt))
twoAgentAggregateExtractionIsSum =
  trans
    (aggregateExtractionIsTwo twoAgentCommonsCounterexample)
    refl

------------------------------------------------------------------------
-- One bad level destroys an unconditional all-level derivation.
------------------------------------------------------------------------

noUnconditionalNestedCommonsPreservation :
  ∀ {Level : Set} →
  Level →
  (C : CommonsNonDerivabilityCounterexample) →
  ¬ NestedCommonsPreservationDerivation Level C
noUnconditionalNestedCommonsPreservation level C D =
  twoNotLeOne
    (transport (λ n → n ≤ succ zero)
      (capacityIsOne C)
      (transport (λ n → succ (succ zero) ≤ n)
        (aggregateExtractionIsTwo C)
        (derive D
          level
          (commonsWorld C)
          (allLocallyOptimal C))))

------------------------------------------------------------------------
-- Concrete two-scale instance: two nested levels are enough to witness
-- the impossibility. The same local/global law is demanded at each level.
------------------------------------------------------------------------

TwoScaleCommonsLevel : Set
TwoScaleCommonsLevel = ⊤ ⊎ ⊤

noUnconditionalNestedCommonsPreservation-twoScale :
  ¬ NestedCommonsPreservationDerivation
      TwoScaleCommonsLevel
      twoAgentCommonsCounterexample
noUnconditionalNestedCommonsPreservation-twoScale =
  noUnconditionalNestedCommonsPreservation
    (inj₁ tt)
    twoAgentCommonsCounterexample

------------------------------------------------------------------------
-- Scale composition rule.
--
-- A nested preservation proof is strictly stronger than a one-level proof:
-- restricting it to any inhabited level yields the corresponding local
-- preservation derivation. Thus adding more levels cannot manufacture the
-- missing local-to-global conservation invariant.
------------------------------------------------------------------------

nestedLevelRestriction :
  ∀ {Level : Set}
  {C : CommonsNonDerivabilityCounterexample} →
  (D : NestedCommonsPreservationDerivation Level C) →
  ∀ level →
  ∀ w →
  (∀ a →
    localOptimal C w a (action C w a)) →
  aggregateExtraction C w ≤
  resourceCapacity C (sharedResource C w)
nestedLevelRestriction D level =
  derive D level

------------------------------------------------------------------------
-- The unconditional graph is therefore closed at the negative boundary:
--
-- local optimality
--   -> individual extraction
--   -> aggregate extraction
--   -X-> preservation
--
-- and recursively:
--
-- level 0 -> level 1 -> ... -> level n
--   with preservation required at every inhabited level.
--
-- No Boolean encoding is involved. The propositions themselves live in Set;
-- ℕ supplies the resource quantities; equality and subst transport the
-- concrete countermodel into the preservation obligation.
------------------------------------------------------------------------


------------------------------------------------------------------------
-- Economic e-graph composition kernel.
--
-- This is a proof-relevant packaging seam, not an unconditional economic
-- convergence theorem. Convergence, stationarity, equilibrium
-- characterization, and representation reconstruction remain explicit
-- inputs. The composition theorem only transports and combines those
-- already-typed witnesses with the semantic e-graph, plan-monoid, and
-- monadic search surfaces.
------------------------------------------------------------------------

record EGraphEconomicConvergenceFixedPointWitness
  (State : Set)
  (update : State → State)
  (fixed : State) : Set₁ where
  constructor eGraphEconomicConvergenceFixedPointWitness
  field
    eventual :
      ∀ s →
      Σ ℕ
        (λ n →
          iterateStep update n s ＝ fixed)
    stationary :
      update fixed ＝ fixed

open EGraphEconomicConvergenceFixedPointWitness public

eGraphEconomicFixedOrbit :
  ∀ {State : Set}
  {update : State → State}
  {fixed : State}
  (W :
    EGraphEconomicConvergenceFixedPointWitness
      State
      update
      fixed) →
  ∀ n →
  iterateStep update n fixed ＝ fixed
eGraphEconomicFixedOrbit W zero = refl
eGraphEconomicFixedOrbit {update = update} W (succ n) =
  trans
    (ap update (eGraphEconomicFixedOrbit W n))
    (stationary W)

record EGraphEconomicRepresentationWitness
  (State Feature : Set)
  (observe : State → Feature)
  (inverse : Feature → State)
  (Continuous : {A B : Set} → (A → B) → Set) : Set₁ where
  constructor eGraphEconomicRepresentationWitness
  field
    reconstruction :
      ContinuousLeftInverseTheorem
        State
        Feature
        observe
        inverse
        Continuous

open EGraphEconomicRepresentationWitness public

eGraphEconomicRepresentationInjective :
  ∀ {State Feature : Set}
  {observe : State → Feature}
  {inverse : Feature → State}
  {Continuous : {A B : Set} → (A → B) → Set}
  (W :
    EGraphEconomicRepresentationWitness
      State
      Feature
      observe
      inverse
      Continuous) →
  ∀ {s t : State} →
  observe s ＝ observe t →
  s ＝ t
eGraphEconomicRepresentationInjective W {s} {t} eq =
  trans
    (sym
      (ContinuousLeftInverseTheorem.leftInverse
        (reconstruction W)
        s))
    (trans
      (ap
        (ContinuousLeftInverseTheorem.inverse
          (reconstruction W))
        eq)
      (ContinuousLeftInverseTheorem.leftInverse
        (reconstruction W)
        t))

record EGraphEconomicWalrasianWitness
  (State Price Allocation : Set)
  (D :
    MegaGeneralizedWalrasianEquilibrium
      State
      Price
      Allocation)
  (priceOf : State → Price)
  (allocationOf : State → Allocation)
  (fixed : State) : Set₁ where
  constructor eGraphEconomicWalrasianWitness
  field
    equilibriumAtFixed :
      equilibrium
        D
        (priceOf fixed)
        (allocationOf fixed)

open EGraphEconomicWalrasianWitness public

record EGraphEconomicComposition
  (Expression State Feature Price Allocation : Set)
  (R :
    EGraphSemanticInterpretation
      Expression
      State)
  (e f : Expression)
  (update : State → State)
  (fixed : State)
  (D :
    MegaGeneralizedWalrasianEquilibrium
      State
      Price
      Allocation)
  (priceOf : State → Price)
  (allocationOf : State → Allocation)
  (observe : State → Feature)
  (inverse : Feature → State)
  (Continuous : {A B : Set} → (A → B) → Set) : Set₁ where
  constructor eGraphEconomicComposition
  field
    semanticPath :
      EGraphSemanticPath R e f
    convergenceFixedPoint :
      EGraphEconomicConvergenceFixedPointWitness
        State
        update
        fixed
    walrasian :
      EGraphEconomicWalrasianWitness
        State
        Price
        Allocation
        D
        priceOf
        allocationOf
        fixed
    representation :
      EGraphEconomicRepresentationWitness
        State
        Feature
        observe
        inverse
        Continuous
    planMonoid :
      AStarPlanMonoidTheorem Expression
    monads :
      AStarHaskellMonadSurface Expression

open EGraphEconomicComposition public

eGraphEconomicSemanticEquality :
  ∀ {Expression State Feature Price Allocation : Set}
  {R :
    EGraphSemanticInterpretation
      Expression
      State}
  {e f : Expression}
  {update : State → State}
  {fixed : State}
  {D :
    MegaGeneralizedWalrasianEquilibrium
      State
      Price
      Allocation}
  {priceOf : State → Price}
  {allocationOf : State → Allocation}
  {observe : State → Feature}
  {inverse : Feature → State}
  {Continuous : {A B : Set} → (A → B) → Set}
  (W :
    EGraphEconomicComposition
      Expression
      State
      Feature
      Price
      Allocation
      R
      e
      f
      update
      fixed
      D
      priceOf
      allocationOf
      observe
      inverse
      Continuous) →
  interpret R e ＝ interpret R f
eGraphEconomicSemanticEquality W =
  eGraph-path-sound R (semanticPath W)

eGraphEconomicComposition-injective :
  ∀ {Expression State Feature Price Allocation : Set}
  {R :
    EGraphSemanticInterpretation
      Expression
      State}
  {e f : Expression}
  {update : State → State}
  {fixed : State}
  {D :
    MegaGeneralizedWalrasianEquilibrium
      State
      Price
      Allocation}
  {priceOf : State → Price}
  {allocationOf : State → Allocation}
  {observe : State → Feature}
  {inverse : Feature → State}
  {Continuous : {A B : Set} → (A → B) → Set}
  (W :
    EGraphEconomicComposition
      Expression
      State
      Feature
      Price
      Allocation
      R
      e
      f
      update
      fixed
      D
      priceOf
      allocationOf
      observe
      inverse
      Continuous) →
  ∀ {s t : State} →
  observe s ＝ observe t →
  s ＝ t
eGraphEconomicComposition-injective W =
  eGraphEconomicRepresentationInjective (representation W)

eGraphEconomicWalrasianEquilibrium :
  ∀ {Expression State Feature Price Allocation : Set}
  {R :
    EGraphSemanticInterpretation
      Expression
      State}
  {e f : Expression}
  {update : State → State}
  {fixed : State}
  {D :
    MegaGeneralizedWalrasianEquilibrium
      State
      Price
      Allocation}
  {priceOf : State → Price}
  {allocationOf : State → Allocation}
  {observe : State → Feature}
  {inverse : Feature → State}
  {Continuous : {A B : Set} → (A → B) → Set}
  (W :
    EGraphEconomicComposition
      Expression
      State
      Feature
      Price
      Allocation
      R
      e
      f
      update
      fixed
      D
      priceOf
      allocationOf
      observe
      inverse
      Continuous) →
  equilibrium D (priceOf fixed) (allocationOf fixed)
eGraphEconomicWalrasianEquilibrium W =
  equilibriumAtFixed (walrasian W)

------------------------------------------------------------------------
-- Combined closure theorem. The products stay typed and independent:
-- semantic equality, eventual convergence, stationarity, generalized
-- Walrasian equilibrium, and representation injectivity. The monoid and
-- monad surfaces are retained in the witness but are not promoted into
-- semantic or economic laws.
------------------------------------------------------------------------

eGraphEconomicComposition-closure :
  ∀ {Expression State Feature Price Allocation : Set}
  {R :
    EGraphSemanticInterpretation
      Expression
      State}
  {e f : Expression}
  {update : State → State}
  {fixed : State}
  {D :
    MegaGeneralizedWalrasianEquilibrium
      State
      Price
      Allocation}
  {priceOf : State → Price}
  {allocationOf : State → Allocation}
  {observe : State → Feature}
  {inverse : Feature → State}
  {Continuous : {A B : Set} → (A → B) → Set}
  (W :
    EGraphEconomicComposition
      Expression
      State
      Feature
      Price
      Allocation
      R
      e
      f
      update
      fixed
      D
      priceOf
      allocationOf
      observe
      inverse
      Continuous) →
  (interpret R e ＝ interpret R f)
  ×
  ((∀ s →
      Σ ℕ
        (λ n →
          iterateStep update n s ＝ fixed))
   ×
   (update fixed ＝ fixed
    ×
    (equilibrium D (priceOf fixed) (allocationOf fixed)
     ×
     (∀ {s t : State} →
      observe s ＝ observe t →
      s ＝ t))))
eGraphEconomicComposition-closure W =
  eGraphEconomicSemanticEquality W
  ,
  (eventual (convergenceFixedPoint W)
  ,
   (stationary (convergenceFixedPoint W)
   ,
    (equilibriumAtFixed (walrasian W)
    ,
     eGraphEconomicRepresentationInjective
       (representation W))))
------------------------------------------------------------------------
-- Unconditional canonical stationary price-law e-graph seam.
--
-- The unconditional core chooses the zero-step price operator. This
-- removes an external price-update input while making the semantic
-- limitation explicit: identity stationarity is not a nontrivial
-- excess-demand adjustment dynamic.
------------------------------------------------------------------------

canonicalStationaryPriceUpdate :
  {Price : Set} →
  Price →
  Price
canonicalStationaryPriceUpdate p = p

canonicalStationaryPriceLaw :
  {Price : Set} →
  ∀ p →
  canonicalStationaryPriceUpdate p ＝ p
canonicalStationaryPriceLaw p = refl

record UnconditionalEGraphEconomicStationaryPriceComposition
  (Expression State Price : Set)
  (R :
    EGraphSemanticInterpretation
      Expression
      State)
  (e f : Expression) : Set₁ where
  constructor unconditionalEGraphEconomicStationaryPriceComposition
  field
    semanticPath :
      EGraphSemanticPath R e f
    stationaryPriceLaw :
      ∀ p →
      canonicalStationaryPriceUpdate p ＝ p

open UnconditionalEGraphEconomicStationaryPriceComposition public

unconditionalEGraphEconomicStationaryPriceClosure :
  ∀ {Expression State Price : Set}
  {R :
    EGraphSemanticInterpretation
      Expression
      State}
  {e f : Expression}
  (W :
    UnconditionalEGraphEconomicStationaryPriceComposition
      Expression
      State
      Price
      R
      e
      f) →
  EGraphSemanticPath R e f ×
  (∀ p →
    canonicalStationaryPriceUpdate p ＝ p)
unconditionalEGraphEconomicStationaryPriceClosure W =
  semanticPath W
  , stationaryPriceLaw W

unconditionalEGraphEconomicStationaryPriceComposition-from-path :
  ∀ {Expression State Price : Set}
  {R :
    EGraphSemanticInterpretation
      Expression
      State}
  {e f : Expression}
  (path : EGraphSemanticPath R e f) →
  UnconditionalEGraphEconomicStationaryPriceComposition
    Expression
    State
    Price
    R
    e
    f
unconditionalEGraphEconomicStationaryPriceComposition-from-path path =
  unconditionalEGraphEconomicStationaryPriceComposition
    path
    canonicalStationaryPriceLaw

------------------------------------------------------------------------
-- E-graph composition node for the finite/discrete candidate-price
-- classifier.
--
-- This transports the certified semantic path together with the existing
-- proof-relevant finite candidate search. The candidate list and its
-- decision procedure remain explicit inputs: the node classifies supplied
-- candidates and does not manufacture a price outside that list.
------------------------------------------------------------------------

record EGraphEconomicFiniteCandidatePriceComposition
  (Expression State Price Allocation : Set)
  (R :
    EGraphSemanticInterpretation
      Expression
      State)
  (e f : Expression)
  (supports : Price → Allocation → Set)
  (allocation : Allocation)
  (decide : ∀ p → FiniteCandidateDecision (supports p allocation))
  (candidates : List Price) : Set₁ where
  constructor eGraphEconomicFiniteCandidatePriceComposition
  field
    semanticPath :
      EGraphSemanticPath R e f
    candidateClassification :
      finiteCandidatePriceSearch
        supports
        allocation
        decide
        candidates

open EGraphEconomicFiniteCandidatePriceComposition public

eGraphEconomicFiniteCandidatePriceClosure :
  ∀ {Expression State Price Allocation : Set}
  {R :
    EGraphSemanticInterpretation
      Expression
      State}
  {e f : Expression}
  {supports : Price → Allocation → Set}
  {allocation : Allocation}
  {decide : ∀ p → FiniteCandidateDecision (supports p allocation)}
  {candidates : List Price}
  (W :
    EGraphEconomicFiniteCandidatePriceComposition
      Expression
      State
      Price
      Allocation
      R
      e
      f
      supports
      allocation
      decide
      candidates) →
  EGraphSemanticPath R e f ×
  FiniteCandidatePriceResult
    Price
    Allocation
    supports
    allocation
eGraphEconomicFiniteCandidatePriceClosure W =
  semanticPath W
  , candidateClassification W

eGraphEconomicFiniteCandidatePriceComposition-from-path :
  ∀ {Expression State Price Allocation : Set}
  {R :
    EGraphSemanticInterpretation
      Expression
      State}
  {e f : Expression}
  {supports : Price → Allocation → Set}
  {allocation : Allocation}
  {decide : ∀ p → FiniteCandidateDecision (supports p allocation)}
  {candidates : List Price}
  (path : EGraphSemanticPath R e f) →
  EGraphEconomicFiniteCandidatePriceComposition
    Expression
    State
    Price
    Allocation
    R
    e
    f
    supports
    allocation
    decide
    candidates
eGraphEconomicFiniteCandidatePriceComposition-from-path path =
  eGraphEconomicFiniteCandidatePriceComposition
    path
    (finiteCandidatePriceSearch
      supports
      allocation
      decide
      candidates)
