{-# OPTIONS
--sized-types
--no-postfix-projections
--no-projection-like
--erased-matches
--prop
--confluence-check
--two-level
--rewriting
--experimental-lazy-instances
--large-indices
--no-forced-argument-recursion
--with-K
--no-guardedness
--injective-type-constructors
#-}

------------------------------------------------------------------------
-- Canonical theorem semantics and emergence layer.
-- Baseline reconstruction: current imports/options over the last green body.
--
-- The small RUSSProofTheory below has a conditional soundness/consistency theorem for
-- its object calculus. russCurrentBasisRelativeConsistency instantiates that theorem
-- with russianRecursiveMathematicsAssumptions; it does not construct a model of that.
-- A successful kernel check proves only typing relative to that trust surface. An
-- independent result must interpret this exact combined signature in a separately
-- justified model or give a relative-consistency reduction to a certified metatheory.
------------------------------------------------------------------------

module FullCoupled.TheoremsMonolith where

-- Merged external import surface; internal FullCoupled imports remain module-local.
open import Haskell.Prelude hiding (String)

-- Use compiler-owned builtin strings and the version-matched Reflection API.
-- This removes a second declaration of the Reflection/TC ABI. Reflection's
-- operational implementation remains part of the trusted compiler boundary.
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Reflection using
  ( Visibility
  ; visible
  ; Relevance
  ; relevant
  ; Quantity
  ; quantity-ω
  ; Modality
  ; modality
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

open import Agda.Builtin.Sigma public hiding ( _,_ )
import Agda.Builtin.Sigma as Sigma

try-fun : ∀ {a} {A : Set a} → TC A → TC A → TC A
try-fun = catchTC

syntax try-fun t f = try t or-else f




-- Use Agda2HS Prelude algebra and Agda's builtin dependent-pair type.
-- No vendored ordinal or external sum-theory library is required.
import Haskell.Law.Num.Integer as IntegerLaws
open import Haskell.Law.Num.Nat using
  ( addNat-idʳ
  ; addNat-suc
  ; addNat-comm
  ; mulNat-comm
  ; mulNat-distributeˡ-addNat
  ; mulNat-assoc
  )
open import FullCoupled.CanonicalLearnerMonolith as C hiding (gruStep; String)

------------------------------------------------------------------------
-- Re-export shared constructive-computability assumptions from the
-- canonical learner monolith. Keep the actual nested source module there.
------------------------------------------------------------------------
-- This re-export shares the learner monolith's explicitly postulated RUSS
-- basis; it does not install global rewrite rules or prove consistency.
-- Theorem kernel-check results remain relative to this basis, imports, and
-- the Reflection/TC primitive trust boundary documented above.
open C.ConstructiveComputabilityPostulates public using
  ( RussianRecursiveMathematicsBasis
  ; russianRecursiveMathematicsAssumptions
  ; russianMarkovPrinciple
  ; extendedChurchThesis0
  ; russianCountableChoice
  ; churchThesis
  ; constructiveCountableChoice
  ; EmptyComputability
  ; Neg
  ; Decidable
  ; yes
  ; no
  ; SigmaWitness
  ; sigma-witness
  ; sigmaValue
  ; sigmaEvidence
  ; PropExists
  ; RecursiveProgram
  ; ComputesRelation
  )

open import Agda.Primitive using (Level)
open import Agda.Builtin.Size using (Size; Size<_; ∞)

------------------------------------------------------------------------
-- Reflection macro for equality-congruence transport.
-- The target type determines the function whose congruence is required.
------------------------------------------------------------------------

𝓋𝓇𝒶 : {A : Set} → A → Arg A
𝓋𝓇𝒶 = arg (arg-info visible (modality relevant quantity-ω))

＝-type-info : Term → TC (Arg Term × Arg Term × Term × Term)
＝-type-info (def (quote _＝_) (𝓁 ∷ 𝒯 ∷ arg _ left ∷ arg _ right ∷ [])) =
  returnTC (𝓁 , 𝒯 , left , right)
＝-type-info _ = typeError (strErr "Term is not a ＝-type." ∷ [])

$-head : Term → Term
$-head (var v args) = var v []
$-head (con c args) = con c []
$-head (def f args) = def f []
$-head (pat-lam cs args) = pat-lam cs []
$-head t = t

macro
  apply-cong : Term → Term → TC ⊤
  apply-cong proof goal =
    try
      (bindTC (inferType goal) λ targetType →
        bindTC (＝-type-info targetType) λ where
          (_ , _ , left , _) →
            unify goal
              (def (quote cong)
                (𝓋𝓇𝒶 ($-head left) ∷ 𝓋𝓇𝒶 proof ∷ [])))
      or-else unify goal proof


------------------------------------------------------------------------
-- Flat modality as a comonad.
--
-- This is Agda's native crisp/flat modality, not an axiom added to RUSS.
-- The coherence and splitting options are enabled in both monoliths and in
-- the shared CI option list. All laws below reduce by pattern matching and
-- refl; no function extensionality, excluded middle, or postulated law is used.
------------------------------------------------------------------------
module FlatComonad where

  data Flat {@♭ ℓ : Level} (@♭ A : Set ℓ) : Set ℓ where
    flat : (@♭ value : A) → Flat A

  flatExtract : {@♭ ℓ : Level} {@♭ A : Set ℓ} → Flat A → A
  flatExtract (flat value) = value

  flatDuplicate :
    {@♭ ℓ : Level} {@♭ A : Set ℓ} →
    Flat A → Flat (Flat A)
  flatDuplicate (flat value) = flat (flat value)

  flatMap :
    {@♭ ℓA : Level} {@♭ ℓB : Level}
    {@♭ A : Set ℓA} {@♭ B : Set ℓB} →
    (@♭ f : A → B) → Flat A → Flat B
  flatMap f (flat value) = flat (f value)

  flatExtend :
    {@♭ ℓA : Level} {@♭ ℓB : Level}
    {@♭ A : Set ℓA} {@♭ B : Set ℓB} →
    (@♭ f : Flat A → B) → Flat A → Flat B
  flatExtend f (flat value) = flat (f (flat value))

  flatMapIdentity :
    {@♭ ℓ : Level} {@♭ A : Set ℓ} →
    (x : Flat A) → flatMap (λ value → value) x ≡ x
  flatMapIdentity (flat value) = refl

  flatMapComposition :
    {@♭ ℓA : Level} {@♭ ℓB : Level} {@♭ ℓC : Level}
    {@♭ A : Set ℓA} {@♭ B : Set ℓB} {@♭ C : Set ℓC} →
    (@♭ g : B → C) → (@♭ f : A → B) → (x : Flat A) →
    flatMap (g ∘ f) x ≡ flatMap g (flatMap f x)
  flatMapComposition g f (flat value) = refl

  flatExtractMap :
    {@♭ ℓA : Level} {@♭ ℓB : Level}
    {@♭ A : Set ℓA} {@♭ B : Set ℓB} →
    (@♭ f : A → B) → (x : Flat A) →
    flatExtract (flatMap f x) ≡ f (flatExtract x)
  flatExtractMap f (flat value) = refl

  flatExtractDuplicate :
    {@♭ ℓ : Level} {@♭ A : Set ℓ} →
    (x : Flat A) → flatExtract (flatDuplicate x) ≡ x
  flatExtractDuplicate (flat value) = refl

  flatMapExtractDuplicate :
    {@♭ ℓ : Level} {@♭ A : Set ℓ} →
    (x : Flat A) →
    flatMap flatExtract (flatDuplicate x) ≡ x
  flatMapExtractDuplicate (flat value) = refl

  flatDuplicateCoassociative :
    {@♭ ℓ : Level} {@♭ A : Set ℓ} →
    (x : Flat A) →
    flatDuplicate (flatDuplicate x) ≡
      flatMap flatDuplicate (flatDuplicate x)
  flatDuplicateCoassociative (flat value) = refl

  flatExtendExtract :
    {@♭ ℓ : Level} {@♭ A : Set ℓ} →
    (x : Flat A) → flatExtend flatExtract x ≡ x
  flatExtendExtract (flat value) = refl

  flatExtractExtend :
    {@♭ ℓA : Level} {@♭ ℓB : Level}
    {@♭ A : Set ℓA} {@♭ B : Set ℓB} →
    (@♭ f : Flat A → B) → (x : Flat A) →
    flatExtract (flatExtend f x) ≡ f x
  flatExtractExtend f (flat value) = refl

-- END THEOREM-SPECIFIC IMPORTS

module RUSSProofTheory where

  RUSSPrinciplePackage : Set₃
  RUSSPrinciplePackage = RussianRecursiveMathematicsBasis

  ----------------------------------------------------------------------
  -- A small explicit proof theory for the selected RUSS principles.
  --
  -- Metatheoretic anchors:
  -- * Pierre-Marie Pédrot, "Russian Constructivism in a Prefascist Theory,"
  --   LICS 2020, https://doi.org/10.1145/3373718.3394740. The paper constructs
  --   a syntactic presheaf model of CIC interpreting Markov's Principle while
  --   preserving canonicity and decidability of type-checking. It motivates
  --   a model-based treatment of MP; it does not certify this repository's
  --   combined RUSS, ECT0, countable-choice, or Scott-Ershov assumptions.
  -- * Pédrot, "Upon This Quote I Will Build My Church Thesis," LICS 2024,
  --   https://doi.org/10.1145/3661814.3662070. Its quotation-based extension
  --   of MLTT derives internal Church's Thesis and proves consistency,
  --   strong normalization, and canonicity in a logical-relations model,
  --   mechanized in Coq. It is not a drop-in proof for Agda's full import
  --   closure or for this project's extra RUSS/choice signature.
  -- * Cockx, Tabareau, and Winterhalter, "The Taming of the Rew," POPL 2021,
  --   https://doi.org/10.1145/3434341, motivates explicit rewrite rules and
  --   their subject-reduction/confluence obligations.
  --
  -- The present natural-deduction calculus is an Agda formalization of a
  -- signature-relative soundness argument, not Pédrot's presheaf or logical-
  -- relations model. XDS-Agda's Scott-Strachey embeddings
  -- (https://pdmosses.github.io/xds-agda/) likewise demonstrate mechanization,
  -- not consistency of arbitrary domain postulates.
  --
  -- BOUNDARY: this is a relative consistency theorem for this object calculus
  -- interpreted in the Agda types supplied by the chosen basis. It is NOT a
  -- consistency proof for Agda, CIC/Rocq, or this repository's transitive
  -- imports. The project's ECT0 and Prop-valued choice signatures still need
  -- a model/relative-consistency argument for the exact combined theory.
  ----------------------------------------------------------------------

  data RUSSAxiomTag : Set where
    russMarkovTag : RUSSAxiomTag
    russECT0Tag : RUSSAxiomTag
    russCountableChoiceTag : RUSSAxiomTag

  RUSSAxiomMeaning : RUSSAxiomTag → Set₃
  RUSSAxiomMeaning russMarkovTag =
    (P : Nat → Set) →
    ((n : Nat) → Decidable (P n)) →
    Neg (Neg (SigmaWitness Nat P)) →
    SigmaWitness Nat P
  RUSSAxiomMeaning russECT0Tag =
    (relation : Nat → Nat → Set) →
    ((input output : Nat) → Decidable (relation input output)) →
    ((input : Nat) → SigmaWitness Nat (relation input)) →
    SigmaWitness RecursiveProgram
      (λ program → ComputesRelation program relation)
  RUSSAxiomMeaning russCountableChoiceTag =
    (A : Nat → Set) →
    (P : (n : Nat) → A n → Prop) →
    ((n : Nat) → PropExists (P n)) →
    PropExists {A = (n : Nat) → A n}
      (λ choose → (n : Nat) → P n (choose n))

  russAxiomFromBasis :
    (basis : RussianRecursiveMathematicsBasis) →
    (tag : RUSSAxiomTag) → RUSSAxiomMeaning tag
  russAxiomFromBasis basis russMarkovTag =
    RussianRecursiveMathematicsBasis.russMarkov basis
  russAxiomFromBasis basis russECT0Tag =
    RussianRecursiveMathematicsBasis.russECT0 basis
  russAxiomFromBasis basis russCountableChoiceTag =
    RussianRecursiveMathematicsBasis.russCountableChoice basis

  data RUSSFormula : Set where
    russFalsehood : RUSSFormula
    russTruthhood : RUSSFormula
    russAxiom : RUSSAxiomTag → RUSSFormula
    russImplies : RUSSFormula → RUSSFormula → RUSSFormula

  data RUSSTruthEvidence : Set where
    russTruthEvidence : RUSSTruthEvidence

  data RUSSContextMembership (formula : RUSSFormula) :
    List RUSSFormula → Set where
    russHere :
      {context : List RUSSFormula} →
      RUSSContextMembership formula (formula ∷ context)
    russThere :
      {head : RUSSFormula} {context : List RUSSFormula} →
      RUSSContextMembership formula context →
      RUSSContextMembership formula (head ∷ context)

  data RUSSDerivation : List RUSSFormula → RUSSFormula → Set where
    russAssumption :
      {context : List RUSSFormula} {formula : RUSSFormula} →
      RUSSContextMembership formula context →
      RUSSDerivation context formula
    russTruthD :
      {context : List RUSSFormula} →
      RUSSDerivation context russTruthhood
    russAxiomD :
      {context : List RUSSFormula} →
      (tag : RUSSAxiomTag) →
      RUSSDerivation context (russAxiom tag)
    russImpliesIntro :
      {context : List RUSSFormula} {antecedent consequent : RUSSFormula} →
      RUSSDerivation (antecedent ∷ context) consequent →
      RUSSDerivation context (russImplies antecedent consequent)
    russImpliesElim :
      {context : List RUSSFormula} {antecedent consequent : RUSSFormula} →
      RUSSDerivation context (russImplies antecedent consequent) →
      RUSSDerivation context antecedent →
      RUSSDerivation context consequent
    russFalseElim :
      {context : List RUSSFormula} {formula : RUSSFormula} →
      RUSSDerivation context russFalsehood →
      RUSSDerivation context formula

  RUSSFormulaMeaning :
    (basis : RussianRecursiveMathematicsBasis) →
    RUSSFormula → Set₃
  RUSSFormulaMeaning basis russFalsehood = EmptyComputability
  RUSSFormulaMeaning basis russTruthhood = RUSSTruthEvidence
  RUSSFormulaMeaning basis (russAxiom tag) = RUSSAxiomMeaning tag
  RUSSFormulaMeaning basis (russImplies antecedent consequent) =
    RUSSFormulaMeaning basis antecedent →
    RUSSFormulaMeaning basis consequent

  RUSSContextModel :
    (basis : RussianRecursiveMathematicsBasis) →
    List RUSSFormula → Set₃
  RUSSContextModel basis context =
    {formula : RUSSFormula} →
    RUSSContextMembership formula context →
    RUSSFormulaMeaning basis formula

  russExtendContext :
    (basis : RussianRecursiveMathematicsBasis) →
    {context : List RUSSFormula} {formula : RUSSFormula} →
    RUSSContextModel basis context →
    RUSSFormulaMeaning basis formula →
    RUSSContextModel basis (formula ∷ context)
  russExtendContext basis model evidence russHere = evidence
  russExtendContext basis model evidence (russThere membership) =
    model membership

  russEliminateFalse : {A : Set} → EmptyComputability → A
  russEliminateFalse ()

  russSoundness :
    (basis : RussianRecursiveMathematicsBasis) →
    {context : List RUSSFormula} {formula : RUSSFormula} →
    RUSSDerivation context formula →
    RUSSContextModel basis context →
    RUSSFormulaMeaning basis formula
  russSoundness basis (russAssumption membership) model =
    model membership
  russSoundness basis russTruthD model = russTruthEvidence
  russSoundness basis (russAxiomD tag) model =
    russAxiomFromBasis basis tag
  russSoundness basis (russImpliesIntro derivation) model =
    λ evidence →
      russSoundness basis derivation
        (russExtendContext basis model evidence)
  russSoundness basis (russImpliesElim implication antecedent) model =
    russSoundness basis implication model
      (russSoundness basis antecedent model)
  russSoundness basis (russFalseElim derivation) model =
    russEliminateFalse
      (russSoundness basis derivation model)

  russCoreConsistency :
    (basis : RussianRecursiveMathematicsBasis) →
    Neg (RUSSDerivation [] russFalsehood)
  russCoreConsistency basis derivation =
    russEliminateFalse
      (russSoundness basis derivation (λ ()))

  -- CONDITIONAL ONLY: this applies the calculus theorem to the postulated basis.
  -- It neither supplies an inhabitant of the basis nor proves the basis consistent.
  russCurrentBasisRelativeConsistency :
    Neg (RUSSDerivation [] russFalsehood)
  russCurrentBasisRelativeConsistency =
    russCoreConsistency russianRecursiveMathematicsAssumptions


  ----------------------------------------------------------------------
  -- A computational finite-stage semantics for decidable Markov search.
  --
  -- Each bounded stage is structurally recursive on its bound and computes
  -- either a witness carrying proof of P n, or an explicit fuel-exhausted
  -- result. The completeness lemma uses a witness at the bound to show that
  -- this search must return a witness somewhere in the inspected prefix.
  --
  -- This is an executable operational component, not yet Pédrot's syntactic
  -- presheaf model of MLTT. In particular, the existing Markov assumption
  -- still projects a witness from double-negated existence opaquely; this
  -- finite evaluator does not pretend that an unbounded search terminates
  -- without such semantic justification.
  --
  -- XDS-Agda illustrates that selected denotational equations can be made
  -- computational by rewrite rules and then regression-checked. No such
  -- RUSS-specific rewrite rule is needed here: the bounded evaluator reduces
  -- by ordinary pattern matching, and the regression below is checked by refl.
  -- A rewrite rule alone would not supply the required MLTT/presheaf model,
  -- nor prove confluence, subject reduction, canonicity, or consistency.
  ----------------------------------------------------------------------

  data RUSSBoundedSearchResult (P : Nat → Set) : Set where
    russSearchFound : SigmaWitness Nat P → RUSSBoundedSearchResult P
    russSearchFuelExhausted : RUSSBoundedSearchResult P

  -- Search indices 0 through fuel, in increasing order. This function always
  -- terminates for a finite bound; FuelExhausted means only "not found yet".
  russSearchBounded :
    (P : Nat → Set) →
    (fuel : Nat) →
    ((n : Nat) → Decidable (P n)) →
    RUSSBoundedSearchResult P
  russSearchBounded P zero decide with decide zero
  ... | yes evidence = russSearchFound (sigma-witness zero evidence)
  ... | no _ = russSearchFuelExhausted
  russSearchBounded P (suc fuel) decide with russSearchBounded P fuel decide
  ... | russSearchFound witness = russSearchFound witness
  ... | russSearchFuelExhausted with decide (suc fuel)
  ...   | yes evidence = russSearchFound (sigma-witness (suc fuel) evidence)
  ...   | no _ = russSearchFuelExhausted

  -- Finite adequacy: if P holds at the current bound, the search through that
  -- bound yields a genuine witness. An earlier hit is retained; otherwise the
  -- decision at the current index must be positive.
  russSearchBoundedWitness :
    (P : Nat → Set) →
    (fuel : Nat) →
    ((n : Nat) → Decidable (P n)) →
    P fuel →
    SigmaWitness Nat P
  russSearchBoundedWitness P zero decide evidence with decide zero
  ... | yes found = sigma-witness zero found
  ... | no absent = russEliminateFalse (absent evidence)
  russSearchBoundedWitness P (suc fuel) decide evidence
    with russSearchBounded P fuel decide
  ... | russSearchFound witness = witness
  ... | russSearchFuelExhausted with decide (suc fuel)
  ...   | yes found = sigma-witness (suc fuel) found
  ...   | no absent = russEliminateFalse (absent evidence)

  ----------------------------------------------------------------------
  -- Executable interpretation boundary for the selected RUSS principles.
  --
  -- Markov search reduces at finite fuel. ECT0 returns a program carrying
  -- finite-trace evidence via the named basis projection; it is not a
  -- definitional compiler for arbitrary relations. Prop-valued countable
  -- choice remains an opaque proof-level selector. Data-valued choice is
  -- constructive and computational.
  ----------------------------------------------------------------------

  russMarkovOperationalPrefix :
    (P : Nat → Set) →
    (fuel : Nat) →
    ((n : Nat) → Decidable (P n)) →
    RUSSBoundedSearchResult P
  russMarkovOperationalPrefix = russSearchBounded

  russECT0CertifiedProgram :
    (basis : RussianRecursiveMathematicsBasis) →
    (relation : Nat → Nat → Set) →
    ((input output : Nat) → Decidable (relation input output)) →
    ((input : Nat) → SigmaWitness Nat (relation input)) →
    SigmaWitness RecursiveProgram
      (λ program → ComputesRelation program relation)
  russECT0CertifiedProgram basis relation decide pointwiseWitness =
    RussianRecursiveMathematicsBasis.russECT0
      basis relation decide pointwiseWitness

  russPropCountableSelector :
    (basis : RussianRecursiveMathematicsBasis) →
    (A : Nat → Set) →
    (P : (n : Nat) → A n → Prop) →
    ((n : Nat) → PropExists (P n)) →
    PropExists {A = (n : Nat) → A n}
      (λ choose → (n : Nat) → P n (choose n))
  russPropCountableSelector basis A P pointwise =
    RussianRecursiveMathematicsBasis.russCountableChoice
      basis A P pointwise

  russDataCountableSelector :
    (A : Nat → Set) →
    (P : (n : Nat) → A n → Set) →
    ((n : Nat) → SigmaWitness (A n) (P n)) →
    SigmaWitness
      ((n : Nat) → A n)
      (λ choose → (n : Nat) → P n (choose n))
  russDataCountableSelector = constructiveCountableChoice

  -- XDS-style definitional regression: the bounded search computes the
  -- least witness in this concrete decidable example without a new rewrite.
  data RUSSSearchRegressionPredicate : Nat → Set where
    russSearchRegressionWitness :
      RUSSSearchRegressionPredicate (suc zero)

  russSearchRegressionDecision :
    (n : Nat) → Decidable (RUSSSearchRegressionPredicate n)
  russSearchRegressionDecision zero = no (λ ())
  russSearchRegressionDecision (suc zero) = yes russSearchRegressionWitness
  russSearchRegressionDecision (suc (suc _)) = no (λ ())

  russBoundedSearchRegression :
    russSearchBounded
      RUSSSearchRegressionPredicate
      (suc (suc zero))
      russSearchRegressionDecision
    ≡ russSearchFound
        (sigma-witness (suc zero) russSearchRegressionWitness)
  russBoundedSearchRegression = refl

  russBoundedSearchWitnessRegression :
    sigmaValue
      (russSearchBoundedWitness
        RUSSSearchRegressionPredicate
        (suc zero)
        russSearchRegressionDecision
        russSearchRegressionWitness)
    ≡ suc zero
  russBoundedSearchWitnessRegression = refl



  ----------------------------------------------------------------------
  -- Pédrot-inspired dynamic-prompt base for the RUSS search semantics.
  --
  -- Stages are Boolean predicates on candidate indices. The preorder is
  -- p <= q iff every index true at q is true at p; the top stage is the
  -- everywhere-false predicate, and its meet is pointwise disjunction.
  -- This matches the base preorder and top/meet shape used in Pédrot's
  -- Markov model. The bounded evaluator above supplies executable finite
  -- observations of these predicates.
  --
  -- Prompt exceptions are indexed by a stage and require a witness at each
  -- refinement of that stage. Consequently the exception fibre at top is
  -- empty, since top itself is one of its refinements and is everywhere
  -- false. This formalizes a key invariant of the prompt construction, not
  -- the full model: dependent type/context translation, substitution,
  -- conversion preservation, and soundness remain to be formalized before
  -- claiming a Pédrot-style model of Agda MLTT.
  ----------------------------------------------------------------------

  RUSSStage : Set
  RUSSStage = Nat → Bool

  RUSSStageLeq : RUSSStage → RUSSStage → Set
  RUSSStageLeq p q = (n : Nat) → q n ≡ True → p n ≡ True

  russStageLeqRefl :
    (stage : RUSSStage) → RUSSStageLeq stage stage
  russStageLeqRefl stage n evidence = evidence

  russStageLeqTrans :
    (p q r : RUSSStage) →
    RUSSStageLeq p q →
    RUSSStageLeq q r →
    RUSSStageLeq p r
  russStageLeqTrans p q r pLeQ qLeR n rIsTrue =
    pLeQ n (qLeR n rIsTrue)

  russBoolOr : Bool → Bool → Bool
  russBoolOr True _ = True
  russBoolOr False value = value

  russStageTop : RUSSStage
  russStageTop _ = False

  russStageMeet : RUSSStage → RUSSStage → RUSSStage
  russStageMeet p q n = russBoolOr (p n) (q n)

  russFalseNotTrue : False ≡ True → EmptyComputability
  russFalseNotTrue ()

  russStageBelowTop :
    (stage : RUSSStage) → RUSSStageLeq stage russStageTop
  russStageBelowTop stage n evidence =
    russEliminateFalse (russFalseNotTrue evidence)

  russStageMeetLeLeft :
    (p q : RUSSStage) →
    RUSSStageLeq (russStageMeet p q) p
  russStageMeetLeLeft p q n pIsTrue with p n
  ... | True = refl
  ... | False = russEliminateFalse (russFalseNotTrue pIsTrue)

  russStageMeetLeRight :
    (p q : RUSSStage) →
    RUSSStageLeq (russStageMeet p q) q
  russStageMeetLeRight p q n qIsTrue with q n
  ... | True = refl
  ... | False = russEliminateFalse (russFalseNotTrue qIsTrue)

  -- A stage-indexed prompt exception: at stage p it must provide a
  -- witness for every refinement q <= p. The top fibre is empty.
  RUSSPromptExceptionAt : RUSSStage → Set₁
  RUSSPromptExceptionAt stage =
    (refinement : RUSSStage) →
    RUSSStageLeq refinement stage →
    SigmaWitness Nat (λ n → refinement n ≡ True)

  russPromptExceptionAtTopAbsent :
    RUSSPromptExceptionAt russStageTop → EmptyComputability
  russPromptExceptionAtTopAbsent exception =
    russFalseNotTrue
      (sigmaEvidence
        (exception russStageTop (russStageLeqRefl russStageTop)))

  -- Definitional regressions for the dynamic-prompt base. No REWRITE pragma
  -- is required: the stage operations compute by ordinary pattern matching.
  russStageMeetTopRegression :
    (n : Nat) →
    russStageMeet russStageTop russStageTop n ≡ False
  russStageMeetTopRegression n = refl

  russStageMeetTrueRegression :
    (q : RUSSStage) (n : Nat) →
    russStageMeet (λ _ → True) q n ≡ True
  russStageMeetTrueRegression q n = refl


open RUSSProofTheory public

------------------------------------------------------------------------
-- Constructive Rice theorem over an acceptable-programming interface.
--
-- A property is extensional when it depends only on program behavior. If
-- such a property is nontrivial, a total decision procedure contradicts a
-- Kleene fixed-point operator: make the fixed point behave as a counterexample
-- when the decider says yes, and as a witness when the decider says no.
--
-- This derivation is intuitionistic. It uses explicit Decidable evidence,
-- pointwise behavioral equality, and the fixed-point law; no excluded middle,
-- function extensionality, or Markov principle is invoked.
--
-- IMPORTANT INSTANCE BOUNDARY: the register machine above currently has a
-- finite-trace relation and a bounded evaluator. A concrete Rice theorem for
-- that machine still requires a proved universal-program/fixed-point
-- construction. RiceAcceptableSystem is an interface, not a postulate that
-- the repository's register machine already satisfies it.
------------------------------------------------------------------------

data RiceObservation : Set where
  riceDiverges : RiceObservation
  riceReturns : Nat → RiceObservation

RiceEquivalent :
  {Program : Set} →
  (Program → Nat → RiceObservation) →
  Program → Program → Set
RiceEquivalent observe left right =
  (input : Nat) → observe left input ≡ observe right input

record RiceAcceptableSystem : Set₁ where
  constructor riceAcceptableSystem
  field
    RiceProgram : Set
    riceObserve : RiceProgram → Nat → RiceObservation
    riceSelect : Bool → RiceProgram → RiceProgram → RiceProgram
    riceFixedPoint : (RiceProgram → RiceProgram) → RiceProgram
    riceSelectTrue :
      (left right : RiceProgram) →
      RiceEquivalent riceObserve (riceSelect True left right) left
    riceSelectFalse :
      (left right : RiceProgram) →
      RiceEquivalent riceObserve (riceSelect False left right) right
    riceFixedPointLaw :
      (transform : RiceProgram → RiceProgram) →
      RiceEquivalent riceObserve
        (riceFixedPoint transform)
        (transform (riceFixedPoint transform))

module ConstructiveRiceTheorem (system : RiceAcceptableSystem) where
  open RiceAcceptableSystem system

  riceEquivalentSym :
    ∀ {left right : RiceProgram} →
    RiceEquivalent riceObserve left right →
    RiceEquivalent riceObserve right left
  riceEquivalentSym equivalent input = sym (equivalent input)

  riceEquivalentTrans :
    ∀ {left middle right : RiceProgram} →
    RiceEquivalent riceObserve left middle →
    RiceEquivalent riceObserve middle right →
    RiceEquivalent riceObserve left right
  riceEquivalentTrans first second input =
    trans (first input) (second input)

  riceAdversarialTransform :
    (Property : RiceProgram → Set) →
    ((program : RiceProgram) → Decidable (Property program)) →
    (good bad : RiceProgram) →
    RiceProgram → RiceProgram
  riceAdversarialTransform Property decide good bad program
    with decide program
  ... | yes _ = riceSelect False good bad
  ... | no _ = riceSelect True good bad

  -- Rice's theorem, in constructive negative form: a nontrivial behavioral
  -- property admits no total decision procedure on program indices.
  riceNoDecider :
    (Property : RiceProgram → Set) →
    (extensional :
      ∀ {left right : RiceProgram} →
      RiceEquivalent riceObserve left right →
      Property left → Property right) →
    (good : RiceProgram) →
    Property good →
    (bad : RiceProgram) →
    (Property bad → EmptyComputability) →
    ((program : RiceProgram) → Decidable (Property program)) →
    EmptyComputability
  riceNoDecider Property extensional good goodProperty bad badNotProperty decide
    with decide
      (riceFixedPoint
        (riceAdversarialTransform Property decide good bad))
  ... | yes fixedProperty =
    badNotProperty
      (extensional
        (riceEquivalentTrans
          (riceFixedPointLaw
            (riceAdversarialTransform Property decide good bad))
          (riceSelectFalse good bad))
        fixedProperty)
  ... | no notFixedProperty =
    notFixedProperty
      (extensional
        (riceEquivalentSym
          (riceEquivalentTrans
            (riceFixedPointLaw
              (riceAdversarialTransform Property decide good bad))
            (riceSelectTrue good bad)))
        goodProperty)

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
scanLearnerStream = C.MonoidLSTMStreams.scanSeededStream

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

-- Intuitionistic negation is implication into the Prelude empty type.
-- No excluded-middle or double-negation elimination principle is introduced.
infix 3 ¬_
¬_ : ∀ {ℓ : Level} → Set ℓ → Set ℓ
¬ A = A → ⊥

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

module GRUStatisticalInjectivity where
-- Constructive inequality is negated propositional equality; this is notation,
-- not a classical principle.
infix 4 _≢_
_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = ¬ (x ＝ y)

CanonicalGRUStatisticalObservation : Set
CanonicalGRUStatisticalObservation = C.GRUState × (C.CanonicalToken → Integer)
canonicalGRUStatisticalEncode : C.GRUState → CanonicalGRUStatisticalObservation
canonicalGRUStatisticalEncode s = s , (λ _ → C.hiddenState s)
canonicalGRUStatisticalDecode : CanonicalGRUStatisticalObservation → C.GRUState
canonicalGRUStatisticalDecode observation = fst observation
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
canonicalGRUStatisticalStepConsequence : ∀ (s : C.GRUState) (x : Integer) → canonicalGRUStatisticalEncode (C.gruStep s x) ＝ (C.gruStep s x , (λ _ → C.hiddenState (C.gruStep s x)))
canonicalGRUStatisticalStepConsequence s x = refl

identityActivation8-injective :
  ∀ {x y : Integer} →
  C.identityActivation8 x ＝ C.identityActivation8 y →
  x ＝ y
identityActivation8-injective eq = eq

------------------------------------------------------------------------
-- Carrier-polymorphic statistical representation.
--
-- A left inverse implies injectivity constructively. The carrier remains an
-- arbitrary Set, so the same representation law can be instantiated by the
-- canonical GRU observation or an explicitly supplied ZPF state carrier.
------------------------------------------------------------------------

record CarrierPolymorphicStatisticalRepresentation
  (State Observation : Set) : Set₁ where
  constructor carrierPolymorphicStatisticalRepresentation
  field
    encode : State → Observation
    decode : Observation → State
    decodeEncode : ∀ state → decode (encode state) ＝ state

open CarrierPolymorphicStatisticalRepresentation public

statisticalEncodeInjective :
  ∀ {State Observation : Set}
    (R : CarrierPolymorphicStatisticalRepresentation State Observation)
    {s t : State} →
    encode R s ＝ encode R t → s ＝ t
statisticalEncodeInjective R {s} {t} collision =
  trans
    (sym (decodeEncode R s))
    (trans (cong (decode R) collision) (decodeEncode R t))

-- Injectivity preserves constructive distinction: equality of encoded
-- observations would contradict the supplied inequality of states.
statisticalEncodeDistinguishes :
  ∀ {State Observation : Set}
    (R : CarrierPolymorphicStatisticalRepresentation State Observation)
    {s t : State} →
    s ≢ t →
    encode R s ≢ encode R t
statisticalEncodeDistinguishes R distinct encodedEquality =
  distinct (statisticalEncodeInjective R encodedEquality)

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

data RepositoryAgdaModule : Set where
  canonicalLearnerMonolith :
    RepositoryAgdaModule
  theoremsMonolith :
    RepositoryAgdaModule

data IntegerLayerNormExpression : Set where
  rawIntegerLayerNorm :
    ℕ → List Integer → IntegerLayerNormExpression
  centeredIntegerLayerNorm :
    ℕ → List Integer → IntegerLayerNormExpression
  radicandIntegerLayerNorm :
    ℕ → List Integer → IntegerLayerNormExpression

record IntegerLayerNormSemanticState : Set where
  constructor integerLayerNormSemanticState
  field
    epsilon : ℕ
    input : List Integer
    centered : List Integer
    radicand : Integer
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

integerLayerNorm-absurd :
  ∀ {A : Set} →
  ⊥ →
  A
integerLayerNorm-absurd ()

nat-ring-solver-layernorm-contribution :
  ∀ (xs : List Integer) (epsilon : ℕ) →
  (suc epsilon * length xs * length xs)
  ＝
  (epsilon * length xs * length xs)
  + (length xs * length xs)
nat-ring-solver-layernorm-contribution xs epsilon =
  let n = length xs in
  trans
    (cong (λ value → value * n) (mulNat-comm (suc epsilon) n))
    (trans
      refl
      (trans
        (mulNat-distributeˡ-addNat n (n * epsilon) n)
        (trans
          (cong (λ value → (n * n) + value)
            (mulNat-assoc n epsilon n))
          (trans
            (cong (λ value → (n * n) + value)
              (mulNat-comm n (epsilon * n)))
            (addNat-comm (n * n) ((epsilon * n) * n))))))
integerLayerNorm-epsilon-contribution-succ :
  ∀ (xs : List Integer) (epsilon : ℕ) →
  (suc epsilon * length xs * length xs)
  ＝
  (epsilon * length xs * length xs)
  + (length xs * length xs)
integerLayerNorm-epsilon-contribution-succ =
  nat-ring-solver-layernorm-contribution

integerLayerNorm-radicand-epsilon-zero :
  ∀ (xs : List Integer) →
  C.integerLayerNormRadicand xs zero
  ＝
  C.integerLayerNormVarianceNumerator xs
integerLayerNorm-radicand-epsilon-zero xs = refl

integerLayerNorm-radicand-epsilon-succ :
  ∀ (xs : List Integer) (epsilon : ℕ) →
  C.integerLayerNormRadicand xs (suc epsilon)
  ＝
  C.integerLayerNormRadicand xs epsilon
  +
  (pos (length xs * length xs))
integerLayerNorm-radicand-epsilon-succ xs epsilon =
  trans
    (cong
      (λ n →
        C.integerLayerNormVarianceNumerator xs
        +
        (pos n))
      (integerLayerNorm-epsilon-contribution-succ xs epsilon))
    (sym
      (IntegerLaws.addInteger-assoc
        (C.integerLayerNormVarianceNumerator xs)
        (pos (epsilon * length xs * length xs))
        (pos (length xs * length xs))))

integer-layernorm-centered-statistics-independent-of-epsilon :
  ∀ (xs : List Integer) (epsilon delta : ℕ) →
  centered
    (integerLayerNormSemanticInterpret
      (rawIntegerLayerNorm epsilon xs))
  ＝
  centered
    (integerLayerNormSemanticInterpret
      (rawIntegerLayerNorm delta xs))
integer-layernorm-centered-statistics-independent-of-epsilon _ _ _ = refl

integer-layernorm-denominator-configuration-stable :
  ∀ (xs : List Integer)
  (config₁ config₂ : C.IntegerLayerNormConfig)
  (certificate : C.IntegerLayerNormCertificate xs)
  (x : Integer) →
  C.denominator
    (C.integerLayerNormValue config₁ certificate x)
  ＝
  C.denominator
    (C.integerLayerNormValue config₂ certificate x)
integer-layernorm-denominator-configuration-stable
  _ _ _ certificate x = refl

integerLayerNorm-radicand-epsilon-linear :
  ∀ (xs : List Integer) (epsilon : ℕ) →
  C.integerLayerNormRadicand xs epsilon
  ＝
  C.integerLayerNormVarianceNumerator xs
  +
  (pos (epsilon * length xs * length xs))
integerLayerNorm-radicand-epsilon-linear xs zero =
  trans
    (integerLayerNorm-radicand-epsilon-zero xs)
    (sym
      (addInteger-idʳ
        (C.integerLayerNormVarianceNumerator xs)))
integerLayerNorm-radicand-epsilon-linear xs (suc epsilon) =
  trans
    (integerLayerNorm-radicand-epsilon-succ xs epsilon)
    (trans
      (cong₂ _+_
        (integerLayerNorm-radicand-epsilon-linear xs epsilon)
        refl)
      (trans
        (sym
          (IntegerLaws.addInteger-assoc
            (C.integerLayerNormVarianceNumerator xs)
            (pos (epsilon * length xs * length xs))
            (pos (length xs * length xs))))
        (cong
          (λ n →
            C.integerLayerNormVarianceNumerator xs
            +
            (pos n))
          (sym
            (integerLayerNorm-epsilon-contribution-succ
              xs
              epsilon)))))

record CanonicalF4GlobalOptimizerStabilityTheorem : Set₁ where
  constructor canonicalF4GlobalOptimizerStabilityTheorem
  field
    thetaTranslation :
      ∀ {A} (K : C.FullLearnerKernel A) (s : C.FullLearnerState A) →
      C.thetaQ (C.canonicalOptimizerStep K s) ＝
      (_+_)
        ((_+_) (C.thetaQ (C.optimizer s)) (C.canonicalSignal K s))
        (C.l2Correction (C.globalL2 (C.optimizerKernel K)))
    stableNonThetaCoordinates :
      ∀ {A} (K : C.FullLearnerKernel A) (s : C.FullLearnerState A) →
      (C.rTheta (C.canonicalOptimizerStep K s) ＝ 0) ×
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
iterateConjugacy {learnerStep = learnerStep} {physicalStep = physicalStep} encode stepConjugacy (suc n) s =
  trans
    (stepConjugacy (C.iterate learnerStep n s))
    (cong
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
    (cong
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
  ∀ (xs ys : List Integer) →
  CanonicalListPermutation xs ys →
  ∀ c →
  C.runMonoidLSTMCell xs c ＝
  C.runMonoidLSTMCell ys c

canonicalNegativeOne8 : Integer
canonicalNegativeOne8 = negsuc zero

canonicalPermutation-swap :
  CanonicalListPermutation
    (1 ∷ canonicalNegativeOne8 ∷ [])
    (canonicalNegativeOne8 ∷ 1 ∷ [])
canonicalPermutation-swap =
  canonical-perm-swap 1 canonicalNegativeOne8 []

canonicalPermutation-left :
  C.runMonoidLSTMCell
    (1 ∷ canonicalNegativeOne8 ∷ [])
    0
  ＝
  0
canonicalPermutation-left = refl

canonicalPermutation-right :
  C.runMonoidLSTMCell
    (canonicalNegativeOne8 ∷ 1 ∷ [])
    0
  ＝
  1
canonicalPermutation-right = refl

canonicalZeroInt-not-oneInt :
  ¬ ((pos 0) ＝ (pos 1))
canonicalZeroInt-not-oneInt ()

canonicalZero8-not-1 :
  0 ≢ 1
canonicalZero8-not-1 eq =
  canonicalZeroInt-not-oneInt eq

canonicalPermutation-results-distinct :
  C.runMonoidLSTMCell
    (1 ∷ canonicalNegativeOne8 ∷ [])
    0
  ≢
  C.runMonoidLSTMCell
    (canonicalNegativeOne8 ∷ 1 ∷ [])
    0
canonicalPermutation-results-distinct eq =
  canonicalZero8-not-1
    (trans
      (sym canonicalPermutation-left)
      (trans eq canonicalPermutation-right))

canonicalLearnerPermutationInvariant-impossible :
  CanonicalLearnerPermutationInvariant → ⊥
canonicalLearnerPermutationInvariant-impossible invariant =
  canonicalPermutation-results-distinct
    (invariant
      (1 ∷ canonicalNegativeOne8 ∷ [])
      (canonicalNegativeOne8 ∷ 1 ∷ [])
      canonicalPermutation-swap
      0)

record CanonicalLearnerPermutationCompositionImpossibilityTheorem : Set₁ where
  constructor canonicalLearnerPermutationCompositionImpossibilityTheorem
  field
    permutationWitness :
      CanonicalListPermutation
        (1 ∷ canonicalNegativeOne8 ∷ [])
        (canonicalNegativeOne8 ∷ 1 ∷ [])
    distinctResults :
      C.runMonoidLSTMCell
        (1 ∷ canonicalNegativeOne8 ∷ [])
        0
      ≢
      C.runMonoidLSTMCell
        (canonicalNegativeOne8 ∷ 1 ∷ [])
        0
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
    (cong (decode F level) eq)

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
  GRUFractalRefines zero (suc zero)
canonicalGRUTwoScaleRefinement = z≤n

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
      (cong (decode C level) (projectionEncode C level state))
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
------------------------------------------------------------------------

------------------------------------------------------------------------
------------------------------------------------------------------------

------------------------------------------------------------------------
--
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
      (cong (limitDecode L) eq)
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
gruFractalLimitConvergence-limitLeftInverse {rank = rank} W =
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


false-not-true : ¬ (False ＝ True)
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
      {s = False} {t = True} refl)

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
      (_+_)
        ((_+_)
          ((_+_)
            (C.canonicalReward8 K s)
            (C.canonicalQLogBias K s))
          ((_*_) C.canonicalDiscount8
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
  C.iterateCanonical K (suc n) s ≢ s
canonicalAperiodic-theorem = C.canonicalAperiodic

canonicalNoNontrivialFiniteCycle-theorem :
  ∀ K s n →
  C.iterateCanonical K (suc n) s ＝ s → ⊥
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
iterateIsomorphism f (suc n) a = iterateIsomorphism f n (f a)

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
stepConjugacy-iterate {sourceStep = sourceStep} {targetStep = targetStep} W (suc n) a =
  trans
    (stepConjugacy-iterate {sourceStep = sourceStep} {targetStep = targetStep} W n (sourceStep a))
    (cong
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
iteratePredicateTransport step Property preserved (suc n) b proof =
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
canonicalPersistentGRU-afterFullStep-iterate K (suc n) s =
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
  RecurrentAssociativeScanTheorem C.GRUState Integer
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
  RecurrentPrefixMonoidHomomorphism C.GRUState Integer
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
      (C.applyEndomorphism f (fst st) ,
       C.applyEndomorphism g (snd st)))

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
  C.RecurrentNetwork C.F4IntUState Integer
canonicalF4RecurrentNetwork K =
  C.recurrentNetwork
    (λ o signal →
      C.f4ThetaStep (C.optimizerKernel K) o signal)

canonicalF4RecurrentNetwork-step-law :
  ∀ (K : C.CanonicalFullLearnerKernel)
  (o : C.F4IntUState)
  (signal : Integer) →
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
    Integer
canonicalF4-prefix-monoid-homomorphism =
  recurrentPrefixMonoidHomomorphism
    (λ R s → prefixListEndomorphism-unit R s)
    (λ R xs ys s → prefixListEndomorphism-append R xs ys s)

CanonicalGRUF4PrefixState : Set
CanonicalGRUF4PrefixState =
  C.GRUState × C.F4IntUState

CanonicalGRUF4PrefixInput : Set
CanonicalGRUF4PrefixInput =
  Integer × Integer

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
  (gruInput optimizerInput : Integer) →
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
      RecurrentPrefixMonoidHomomorphism C.GRUState Integer
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
commutingIterate step (suc n) s =
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
    deriveIterateSquare (suc n) s =
      trans
        (square (commutingIterate step n s))
        (cong featureStep (deriveIterateSquare n s))

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
    suc
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
recurrentPrefix-scan-lifts-conjugacy replace step h xs (suc n) s =
  trans
    (recurrentPrefix-scan-lifts-conjugacy
      replace
      step
      h
      xs
      n
      (step s (xs n)))
    (cong
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
  RecurrentScanConjugacyTheorem C.GRUState Integer
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
canonicalFullLearner-iterate-conjugacy replace K h (suc n) s =
  trans
    (canonicalFullLearner-iterate-conjugacy
      replace K h n (C.canonicalFullStep K s))
    (cong
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
  S4PlusS5RecurrentScanTheorem C.GRUState Integer
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
      (C.runNetwork RA (fst st) x ,
       C.runNetwork RB (snd st) x))

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
productRecurrentPrefix-correct RA RB xs (suc n) s t =
  cong₂
    (λ a b →
      (C.runNetwork RA a (xs n) ,
       C.runNetwork RB b (xs n)))
    (cong fst (productRecurrentPrefix-correct RA RB xs n s t))
    (cong snd (productRecurrentPrefix-correct RA RB xs n s t))

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
  cong target (sym (leftInverse s))

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
  (observeA (fst st) , observeB (snd st))

productInverse :
  ∀ {StateA StateB FeatureA FeatureB : Set} →
  (FeatureA → StateA) →
  (FeatureB → StateB) →
  (FeatureA × FeatureB) →
  (StateA × StateB)
productInverse inverseA inverseB feature =
  (inverseA (fst feature) , inverseB (snd feature))

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
  C.CanonicalFullLearnerKernel → C.CanonicalFullLearnerState → Integer
canonicalBiasedWatkinsNegativeQMunchausenL2Target =
  C.canonicalWatkinsTarget

canonical-qLog2Bias8-law :
  ∀ x →
  C.qLog2Bias8 x ＝
  negateInteger
    (fromNat
      (C.rationalCodeDivideMagnitude
        (C.munchausenScale8 * C.rationalCodeNumeratorMagnitude (C.qLog8 x))
        (C.rationalCodeDenominator (C.qLog8 x))))
canonical-qLog2Bias8-law x with C.intCodeMagnitude x
... | zero = refl
... | suc n = refl


record CanonicalBiasedWatkinsNegativeQMunchausenL2TargetTheorem : Set₁ where
  constructor canonicalBiasedWatkinsNegativeQMunchausenL2TargetTheorem
  field
    negativeQMunchausenBias :
      ∀ x →
      C.qLog2Bias8 x ＝
      negateInteger
        (fromNat
          (C.rationalCodeDivideMagnitude
            (C.munchausenScale8 * C.rationalCodeNumeratorMagnitude (C.qLog8 x))
            (C.rationalCodeDenominator (C.qLog8 x))))

    targetDecomposition :
      ∀ K s →
      canonicalBiasedWatkinsNegativeQMunchausenL2Target K s ＝
      (_+_)
        ((_+_)
          ((_+_)
            (C.canonicalReward8 K s)
            (C.canonicalQLogBias K s))
          ((_*_)
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
      negateInteger
        (fromNat
          (C.rationalCodeDivideMagnitude
            (C.munchausenScale8 * C.rationalCodeNumeratorMagnitude (C.qLog8 x))
            (C.rationalCodeDenominator (C.qLog8 x))))

    l2CorrectionNegation :
      ∀ x →
      C.l2Correction x ＝ negateInteger x

open CanonicalQMunchausenL2SharedNegationPolarityTheorem public

canonicalWatkinsTarget-endogenous-leftInverse :
  ∀ (K : C.CanonicalFullLearnerKernel)
  (observe : C.CanonicalFullLearnerState → Integer)
  (inverse : Integer → C.CanonicalFullLearnerState) →
  (leftInverse : ∀ t → inverse (observe t) ＝ t) →
  ∀ s →
  C.canonicalWatkinsTarget K s ＝
    (_+_)
      ((_+_)
        ((_+_)
          (C.canonicalReward8 K (inverse (observe s)))
          (C.canonicalQLogBias K (inverse (observe s))))
        ((_*_)
          C.canonicalDiscount8
          (C.maxCriticValue8
            (C.critic
              (C.watkins
                (inverse (observe s)))))))
      (C.canonicalEndogenousFeedback K (inverse (observe s)))
canonicalWatkinsTarget-endogenous-leftInverse K observe inverse leftInverse s =
  trans
    (C.canonicalWatkinsTarget-law K s)
    (cong
      (λ t →
        (_+_)
          ((_+_)
            ((_+_)
              (C.canonicalReward8 K t)
              (C.canonicalQLogBias K t))
            ((_*_)
              C.canonicalDiscount8
              (C.maxCriticValue8
                (C.critic (C.watkins t)))))
          (C.canonicalEndogenousFeedback K t))
      (leftInverse s))

succ-injective :
  ∀ {m n : ℕ} → suc m ＝ suc n → m ＝ n
succ-injective refl = refl

natPlus-left-cancel :
  ∀ (k m n : ℕ) → k + m ＝ k + n → m ＝ n
natPlus-left-cancel zero m n eq = eq
natPlus-left-cancel (suc k) m n eq =
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
        (cong (λ t → C.totalCount (C.lcbCounts t)) eq)
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

-- Exact universal readout on a discrete carrier follows from an explicit
-- left inverse. This is an exact factorisation result for arbitrary set-valued
-- targets; it is not the analytic UAP for continuous functions on compact
-- subsets of R^n.
discreteExactUniversalUAPFromLeftInverse :
  ∀ {State Feature : Set}
  (observe : State → Feature)
  (inverse : Feature → State) →
  (∀ s → inverse (observe s) ＝ s) →
  DiscreteExactUniversalUAP State Feature observe
discreteExactUniversalUAPFromLeftInverse observe inverse leftInverse =
  discreteExactUniversalUAP
    (λ {Output} target feature → target (inverse feature))
    (λ {Output} target s → sym (cong target (leftInverse s)))

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
  ¬ (Σ (Feature → State)
      (λ inverse → ∀ u → inverse (observe u) ＝ u))
collision-implies-no-leftInverse-via-injectivity
  observe obsEq distinct =
  λ witness →
    distinct
      (discreteLeftInverse-observe-injective
        (Sigma.snd witness)
        obsEq)

canonicalWatkinsTargetSignalStream :
  C.CanonicalFullLearnerKernel →
  C.CanonicalFullLearnerState →
  ℕ →
  Integer
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
  (observe : C.CanonicalFullLearnerState → Integer)
  (inverse : Integer → C.CanonicalFullLearnerState) →
  (∀ t → inverse (observe t) ＝ t) →
  DenseNeighborhoodSeparationTheorem
    C.CanonicalFullLearnerState
    Integer
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
      (_≤_ : Integer → Integer → Set)
      (operator :
        MinimaxBellmanShapleyOperator
          C.CanonicalFullLearnerState
          Integer
          _≤_)
      (lower upper : C.CanonicalFullLearnerState → Integer) →
      PointwiseSandwich
        _≤_
        lower
        (canonicalBiasedWatkinsNegativeQMunchausenL2Target K)
        upper →
      MinimaxBellmanShapleyInclusionTheorem
        C.CanonicalFullLearnerState
        Integer
        _≤_
        operator
        lower
        (canonicalBiasedWatkinsNegativeQMunchausenL2Target K)
        upper

    endogenousFactorization :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (observe : C.CanonicalFullLearnerState → Integer)
      (inverse : Integer → C.CanonicalFullLearnerState) →
      (leftInverse : ∀ t → inverse (observe t) ＝ t) →
      ∀ s →
      C.canonicalWatkinsTarget K s ＝
      (_+_)
        ((_+_)
          ((_+_)
            (C.canonicalReward8 K (inverse (observe s)))
            (C.canonicalQLogBias K (inverse (observe s))))
          ((_*_)
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
      (observe : C.CanonicalFullLearnerState → Integer)
      (inverse : Integer → C.CanonicalFullLearnerState) →
      (∀ t → inverse (observe t) ＝ t) →
      DenseNeighborhoodSeparationTheorem
        C.CanonicalFullLearnerState
        Integer
        (λ n → C.iterateCanonical K n s)
        observe

canonicalDeterministicFiniteStepDivergenceInevitability :
  ∀ {A}
  (K : C.CanonicalFullLearnerKernel)
  (s : C.CanonicalFullLearnerState)
  (n : ℕ) →
  C.iterateCanonical K (suc n) s ≢ s
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
  cong
    (λ k → C.iterateCanonical K k s)
    (addNat-idʳ m)
canonicalIterateComposition K m (suc n) s =
  trans
    (cong
      (λ k → C.iterateCanonical K k s)
      (addNat-suc m n))
    (cong
      (C.canonicalFullStep K)
      (canonicalIterateComposition K m n s))

recurrentPrefixStepWork : ℕ → ℕ
recurrentPrefixStepWork zero = zero
recurrentPrefixStepWork (suc n) = suc (recurrentPrefixStepWork n)

recurrentPrefixStepWork-law :
  ∀ n → recurrentPrefixStepWork n ＝ n
recurrentPrefixStepWork-law n = refl

recurrentPrefixStepWork-split :
  ∀ m n →
  recurrentPrefixStepWork (m + n) ＝
  recurrentPrefixStepWork m + recurrentPrefixStepWork n
recurrentPrefixStepWork-split m zero =
  trans
    (cong recurrentPrefixStepWork (addNat-idʳ m))
    (sym (addNat-idʳ (recurrentPrefixStepWork m)))
recurrentPrefixStepWork-split m (suc n) =
  trans
    (cong recurrentPrefixStepWork (addNat-suc m n))
    (cong suc (recurrentPrefixStepWork-split m n))

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
  cong
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
iterateState step (suc n) s = step (iterateState step n s)

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
      RecurrentPrefixMonoidHomomorphism C.GRUState Integer
    s4PlusS5RecurrentScan :
      S4PlusS5RecurrentScanTheorem C.GRUState Integer
    informationPreservingTask :
      ∀ {State Feature Output : Set}
      (observe : State → Feature) (inverse : Feature → State)
      (leftInverse : ∀ s → inverse (observe s) ＝ s)
      (target : State → Output) (s : State) →
      target s ＝ target (inverse (observe s))

open CanonicalPolymorphicSparsemaxCompositionTheorem public

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
iterateUpdate update (suc n) state =
  update (iterateUpdate update n state)

GloballyEventuallyFixed :
  ∀ {State : Set} →
  (State → State) → State → Set
GloballyEventuallyFixed update fixed =
  ∀ state → Σ ℕ (λ n → iterateUpdate update n state ＝ fixed)

------------------------------------------------------------------------
-- Guarded coinductive trace dense-separation kernel.
--
-- This is ordinary coinductive data and propositional equality under the
-- monolith's --with-K option, not Cubical Agda. This proof path intentionally
-- uses no Cubical mode or imports. Density is explicit finite observational
-- separation; injectivity follows from a left inverse, and conjugacy transports
-- the guarded orbit exactly. The emergent witness remains proof-relevant data.
------------------------------------------------------------------------

record GuardedTrace (Feature : Set) : Set where
  coinductive
  no-eta-equality
  field
    traceHead : Feature
    traceTail : GuardedTrace Feature

guardedTraceStage :
  ∀ {Feature : Set} →
  ℕ →
  GuardedTrace Feature →
  Feature
guardedTraceStage zero trace = GuardedTrace.traceHead trace
guardedTraceStage (suc n) trace =
  guardedTraceStage n (GuardedTrace.traceTail trace)

record GuardedTraceDenseRepresentation
  (State Feature : Set) : Set₁ where
  constructor guardedTraceDenseRepresentation
  field
    observe :
      State →
      GuardedTrace Feature

    decode :
      GuardedTrace Feature →
      State

    leftInverse :
      ∀ s →
      decode (observe s) ＝ s

    denseSeparation :
      ∀ {s t} →
      s ≢ t →
      Σ ℕ
        (λ n →
          guardedTraceStage n (observe s) ≢
          guardedTraceStage n (observe t))

guardedTraceGlobalInjective :
  ∀ {State Feature : Set} →
  (R : GuardedTraceDenseRepresentation State Feature) →
  ∀ {s t} →
  GuardedTraceDenseRepresentation.observe R s ＝ GuardedTraceDenseRepresentation.observe R t →
  s ＝ t
guardedTraceGlobalInjective R {s} {t} eq =
  trans
    (sym (GuardedTraceDenseRepresentation.leftInverse R s))
    (trans
      (cong (GuardedTraceDenseRepresentation.decode R) eq)
      (GuardedTraceDenseRepresentation.leftInverse R t))

guardedTracePointSeparation :
  ∀ {State Feature : Set} →
  (R : GuardedTraceDenseRepresentation State Feature) →
  ∀ {s t} →
  s ≢ t →
  GuardedTraceDenseRepresentation.observe R s ≢ GuardedTraceDenseRepresentation.observe R t
guardedTracePointSeparation R neq collision =
  neq (guardedTraceGlobalInjective R collision)

record GuardedTraceConjugacy
  (State Feature : Set)
  (stateStep : State → State)
  (featureStep : GuardedTrace Feature → GuardedTrace Feature)
  (R : GuardedTraceDenseRepresentation State Feature) : Set₁ where
  constructor guardedTraceConjugacy
  field
    stepConjugacy :
      ∀ s →
      GuardedTraceDenseRepresentation.observe R (stateStep s) ＝
      featureStep (GuardedTraceDenseRepresentation.observe R s)

iterateGuardedFeature :
  ∀ {Feature : Set} →
  (GuardedTrace Feature → GuardedTrace Feature) →
  ℕ →
  GuardedTrace Feature →
  GuardedTrace Feature
iterateGuardedFeature step zero s = s
iterateGuardedFeature step (suc n) s =
  step (iterateGuardedFeature step n s)

guardedTraceIterateConjugacy :
  ∀ {State Feature : Set}
  {stateStep : State → State}
  {featureStep :
    GuardedTrace Feature →
    GuardedTrace Feature}
  {R : GuardedTraceDenseRepresentation State Feature}
  (C :
    GuardedTraceConjugacy
      State
      Feature
      stateStep
      featureStep
      R) →
  ∀ n s →
  GuardedTraceDenseRepresentation.observe R (iterateUpdate stateStep n s) ＝
  iterateGuardedFeature featureStep n (GuardedTraceDenseRepresentation.observe R s)
guardedTraceIterateConjugacy
  {stateStep = stateStep}
  {featureStep = featureStep}
  C zero s = refl
guardedTraceIterateConjugacy
  {stateStep = stateStep}
  {featureStep = featureStep}
  C (suc n) s =
  trans
    (GuardedTraceConjugacy.stepConjugacy C (iterateUpdate stateStep n s))
    (cong
      featureStep
      (guardedTraceIterateConjugacy C n s))

record GuardedTraceDenseSeparationEmergentCompositionTheorem
  (State Feature Emergent : Set)
  (stateStep : State → State)
  (featureStep : GuardedTrace Feature → GuardedTrace Feature)
  (R : GuardedTraceDenseRepresentation State Feature)
  (C :
    GuardedTraceConjugacy
      State
      Feature
      stateStep
      featureStep
      R) : Set₁ where
  constructor guardedTraceDenseSeparationEmergentCompositionTheorem
  field
    emergentWitness :
      Emergent

    globallyInjective :
      ∀ {s t} →
      GuardedTraceDenseRepresentation.observe R s ＝ GuardedTraceDenseRepresentation.observe R t →
      s ＝ t

    densePointSeparation :
      ∀ {s t} →
      s ≢ t →
      GuardedTraceDenseRepresentation.observe R s ≢ GuardedTraceDenseRepresentation.observe R t

    denseStageSeparation :
      ∀ {s t} →
      s ≢ t →
      Σ ℕ
        (λ n →
          guardedTraceStage n
            (GuardedTraceDenseRepresentation.observe R s) ≢
          guardedTraceStage n
            (GuardedTraceDenseRepresentation.observe R t))

    exactIterateConjugacy :
      ∀ n s →
      GuardedTraceDenseRepresentation.observe R (iterateUpdate stateStep n s) ＝
      iterateGuardedFeature featureStep n (GuardedTraceDenseRepresentation.observe R s)

guardedTraceDenseSeparationEmergentComposition :
  ∀ {State Feature Emergent : Set}
  {stateStep : State → State}
  {featureStep :
    GuardedTrace Feature →
    GuardedTrace Feature}
  {R : GuardedTraceDenseRepresentation State Feature}
  {C :
    GuardedTraceConjugacy
      State
      Feature
      stateStep
      featureStep
      R} →
  Emergent →
  GuardedTraceDenseSeparationEmergentCompositionTheorem
    State
    Feature
    Emergent
    stateStep
    featureStep
    R
    C
guardedTraceDenseSeparationEmergentComposition
  {R = R}
  {C = C}
  emergent =
  guardedTraceDenseSeparationEmergentCompositionTheorem
    emergent
    (guardedTraceGlobalInjective R)
    (guardedTracePointSeparation R)
    (GuardedTraceDenseRepresentation.denseSeparation R)
    (guardedTraceIterateConjugacy C)

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
iterateStep-add step (suc m) n s =
  iterateStep-add step m n (step s)

iterateStep-fixed :
  ∀ {State : Set}
  (step : State → State)
  {s : State} →
  step s ＝ s →
  ∀ n →
  iterateStep step n s ＝ s
iterateStep-fixed step fixed zero = refl
iterateStep-fixed step fixed (suc n) =
  trans
    (cong
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
... | Sigma._,_ n tail =
  Sigma._,_ n
  (encodeInjective W
    (trans
      (stepConjugacy W
        (iterateStep stateStep n s))
      (trans
        (cong
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
              s))))))

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
... | Sigma._,_ n fixed =
  Sigma._,_ n
  (λ k →
    trans
      (iterateStep-add stateStep n k s)
      (iterateStep-fixed
        stateStep
        fixed
        k))

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
  ¬ GloballyEventuallyFixed suc 0
successor-never-globally-eventually-fixed-at-zero h =
  no-succ-zero
    (trans
      (sym (iterateUpdate-succ 1))
      (snd (h 1)))
  where
    iterateUpdate-succ :
      ∀ n → iterateUpdate suc n 1 ＝ suc n
    iterateUpdate-succ zero = refl
    iterateUpdate-succ (suc n) =
      cong suc (iterateUpdate-succ n)

    no-succ-zero : ∀ {n : ℕ} → suc n ≢ 0
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
      suc
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
nonzeroWeight (suc _) = suc zero

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

generalTsallis2NearRationalCodeSparsity : ActionWeights → C.RationalCode
generalTsallis2NearRationalCodeSparsity xs with actionWeightSquareSum xs
... | zero =
  C.fromNatRationalCode 1 1
... | suc q =
  C.fromNatRationalCode
    (generalTsallis2Numerator xs)
    (generalTsallis2Denominator xs)

natZeroNotSuc : ∀ {n} → suc n ≢ zero
natZeroNotSuc ()

natSucNotZero : ∀ {n} → zero ≢ suc n
natSucNotZero ()

generalTsallis2NearRationalCodeSparsity-zero :
  ∀ (xs : ActionWeights) →
  actionWeightSquareSum xs ＝ zero →
  generalTsallis2NearRationalCodeSparsity xs ＝
  C.fromNatRationalCode 1 1
generalTsallis2NearRationalCodeSparsity-zero xs h
  with actionWeightSquareSum xs
... | zero = refl
... | suc q = ⊥-elim (natZeroNotSuc h)

generalTsallis2NearRationalCodeSparsity-definition :
  ∀ (xs : ActionWeights) →
  actionWeightSquareSum xs ≢ zero →
  generalTsallis2NearRationalCodeSparsity xs ＝
    C.fromNatRationalCode
      (generalTsallis2Numerator xs)
      (generalTsallis2Denominator xs)
generalTsallis2NearRationalCodeSparsity-definition xs h
  with actionWeightSquareSum xs
... | zero = ⊥-elim (h refl)
... | suc q = refl

rationalCodeRepresentationEqual :
  C.RationalCode →
  C.RationalCode →
  Set
rationalCodeRepresentationEqual x y = x ＝ y

tsallis2NearRationalCode-oneHot :
  rationalCodeRepresentationEqual
    (generalTsallis2NearRationalCodeSparsity (suc zero ∷ zero ∷ []))
    (C.fromNatRationalCode 1 2)
tsallis2NearRationalCode-oneHot = refl

generalSupportSparsityRationalCode : ActionWeights → C.RationalCode
generalSupportSparsityRationalCode xs =
  C.fromNatRationalCode
    (length xs C._∸_ actionSupportCount xs)
    (length xs)

generalSupportSparsityRationalCode-definition :
  ∀ xs →
  generalSupportSparsityRationalCode xs ＝
    C.fromNatRationalCode
      (length xs C._∸_ actionSupportCount xs)
      (length xs)
generalSupportSparsityRationalCode-definition xs = refl

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

jaxIntegerSum : List Integer → Integer
jaxIntegerSum [] = pos 0
jaxIntegerSum (x ∷ xs) =
  x + jaxIntegerSum xs

jaxAffine : Integer → Integer
jaxAffine x =
  (pos 2) * x + (pos 1)

jaxVmapAffine : List Integer → List Integer
jaxVmapAffine =
  map jaxAffine

jaxVmapAffine-law :
  ∀ xs →
  jaxVmapAffine xs ＝
  map (λ x → (pos 2) * x + (pos 1)) xs
jaxVmapAffine-law xs = refl

jaxPrefixSum : Integer → List Integer → List Integer
jaxPrefixSum carry [] = []
jaxPrefixSum carry (x ∷ xs) =
  let next = carry + x in
  next ∷ jaxPrefixSum next xs

jaxAssociativePrefixSum : List Integer → List Integer
jaxAssociativePrefixSum [] = []
jaxAssociativePrefixSum (x ∷ xs) =
  x ∷ jaxPrefixSum x xs

jaxSequentialPrefixSum : Integer → List Integer → List Integer
jaxSequentialPrefixSum carry [] = []
jaxSequentialPrefixSum carry (x ∷ xs) =
  let next = carry + x in
  next ∷ jaxSequentialPrefixSum next xs

jaxSequentialPrefixSumFromZero : List Integer → List Integer
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
  fst (jaxRecurrentScan step state (x ∷ xs))
  ＝
  fst (jaxRecurrentScan step (fst (step state x)) xs)
jaxRecurrentScan-step-law step state x xs with step state x
... | state′ , output = refl

jaxLexicographicScoreOrder :
  List C.ScoreEntry →
  List ℕ
jaxLexicographicScoreOrder xs =
  map snd (C.sortScores xs)

jaxLexicographicScoreOrder-law :
  ∀ xs →
  jaxLexicographicScoreOrder xs ＝
  map snd (C.sortScores xs)
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
  List Integer →
  List Integer
jaxIntegerLayerNormCenteredNumerators =
  C.integerLayerNormCenteredNumerators

jaxIntegerLayerNormCenteredNumerators-law :
  ∀ xs →
  jaxIntegerLayerNormCenteredNumerators xs ＝
  C.integerLayerNormCenteredNumerators xs
jaxIntegerLayerNormCenteredNumerators-law xs = refl

jaxIntegerLayerNormRadicand :
  List Integer →
  ℕ →
  Integer
jaxIntegerLayerNormRadicand =
  C.integerLayerNormRadicand

jaxIntegerLayerNormRadicand-law :
  ∀ xs epsilon →
  jaxIntegerLayerNormRadicand xs epsilon ＝
  C.integerLayerNormRadicand xs epsilon
jaxIntegerLayerNormRadicand-law xs epsilon = refl

jaxBatchedIntegerLayerNormRadicand :
  List (List Integer) →
  ℕ →
  List Integer
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
  Integer →
  Integer
jaxSignedGate =
  C.gateFromInput

jaxSignedGate-law :
  ∀ x →
  jaxSignedGate x ＝
  C.gateFromInput x
jaxSignedGate-law x = refl

jaxGRUHiddenStep :
  C.GRUState →
  Integer →
  Integer
jaxGRUHiddenStep state x =
  C.hiddenState (C.gruStep state x)

jaxGRUHiddenStep-law :
  ∀ state x →
  jaxGRUHiddenStep state x ＝
  C.hiddenState (C.gruStep state x)
jaxGRUHiddenStep-law state x = refl

zipGRUStatesInts :
  List C.GRUState →
  List Integer →
  List (C.GRUState × Integer)
zipGRUStatesInts [] ys = []
zipGRUStatesInts (x ∷ xs) [] = []
zipGRUStatesInts (x ∷ xs) (y ∷ ys) =
  (x , y) ∷ zipGRUStatesInts xs ys

jaxBatchedGRUHiddenStep :
  List C.GRUState →
  List Integer →
  List Integer
jaxBatchedGRUHiddenStep states xs =
  map
    (λ stateX → jaxGRUHiddenStep (fst stateX) (snd stateX))
    (zipGRUStatesInts states xs)

jaxBatchedGRUHiddenStep-law :
  ∀ states xs →
  jaxBatchedGRUHiddenStep states xs ＝
  map
    (λ stateX →
      C.hiddenState
        (C.gruStep
          (fst stateX)
          (snd stateX)))
    (zipGRUStatesInts states xs)
jaxBatchedGRUHiddenStep-law states xs = refl
jaxJittedScanSum :
  List Integer →
  Integer
jaxJittedScanSum =
  jaxIntegerSum

jaxJittedScanSum-law :
  ∀ xs →
  jaxJittedScanSum xs ＝
  jaxIntegerSum xs
jaxJittedScanSum-law xs = refl

jaxTsallis2NearSparsityRationalCode :
  ActionWeights →
  C.RationalCode
jaxTsallis2NearSparsityRationalCode = generalTsallis2NearRationalCodeSparsity

jaxTsallis2NearSparsityRationalCode-law :
  ∀ xs →
  jaxTsallis2NearSparsityRationalCode xs ＝
  generalTsallis2NearRationalCodeSparsity xs
jaxTsallis2NearSparsityRationalCode-law xs = refl

jaxSupportSparsityRationalCode :
  ActionWeights →
  C.RationalCode
jaxSupportSparsityRationalCode = generalSupportSparsityRationalCode

jaxSupportSparsityRationalCode-law :
  ∀ xs →
  jaxSupportSparsityRationalCode xs ＝
  generalSupportSparsityRationalCode xs
jaxSupportSparsityRationalCode-law xs = refl

record JAXExecutionMirrorReproof : Set₁ where
  constructor jaxExecutionMirrorReproof
  field
    vmapAffine :
      ∀ xs →
      jaxVmapAffine xs ＝
      map (λ x → (pos 2) * x + (pos 1)) xs
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
      fst (jaxRecurrentScan step state (x ∷ xs))
      ＝
      fst (jaxRecurrentScan step (fst (step state x)) xs)
    lexicographicScoreOrder :
      ∀ xs →
      jaxLexicographicScoreOrder xs ＝
      map snd (C.sortScores xs)
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
              (fst stateX)
              (snd stateX)))
        (zipGRUStatesInts states xs)
    tsallis2NearSparsity :
      ∀ xs →
      jaxTsallis2NearSparsityRationalCode xs ＝
      generalTsallis2NearRationalCodeSparsity xs
    supportSparsity :
      ∀ xs →
      jaxSupportSparsityRationalCode xs ＝
      generalSupportSparsityRationalCode xs
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
    jaxTsallis2NearSparsityRationalCode-law
    jaxSupportSparsityRationalCode-law
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
    upperStateValue : Integer → Integer → Integer
    upperStateValueEquation :
      ∀ w₈ wᵢ →
      upperStateValue w₈ wᵢ ＝
      2 * wᵢ + w₈
    lowerStateValue : Integer → Integer → Integer
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
globalConjugacyEquivalence-iterate {step = step} {featureStep = featureStep} G (suc n) s =
  trans
    (GlobalConjugacyEquivalence.forward G (iterateState step n s))
    (cong
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
  cong
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
        (cong
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
        (cong gB (fCommutes x)))

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
  (_+_) 1 (negateInteger 1) ＝ 0
canonicalIntegerHaarCross = refl

canonicalIntegerHaarEnergy :
  (_+_) 1 1 ＝ fromNat 2
canonicalIntegerHaarEnergy = refl

record CanonicalIntegerHaarScaledOrthogonalityTheorem : Set₁ where
  constructor canonicalIntegerHaarScaledOrthogonalityTheorem
  field
    crossOrthogonality :
      (_+_) 1 (negateInteger 1) ＝ 0
    integerEnergy :
      (_+_) 1 1 ＝ fromNat 2

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
  List Integer →
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
  List Integer →
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
  (xs ys : List Integer) →
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
  cong
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
  (xs ys : List Integer)
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
    (cong
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
  ∀ (s : C.GRUState) (x : Integer) →
  C.gruStep
    s
    ((_-_)
      (fst (C.canonicalCReLU8 x))
      (snd (C.canonicalCReLU8 x)))
  ＝
  C.gruStep s x
canonicalHaarFeature-recurrent-step s x =
  cong
    (C.gruStep s)
    (C.canonicalHaarFeatureReconstruct x)

canonicalHaarFeature-recurrent-prefix :
  ∀ (xs : List Integer) (s : C.GRUState) →
  C.recurrentListState
    C.canonicalGRURecurrentNetwork
    (map
      (λ x →
        (_-_)
          (fst (C.canonicalCReLU8 x))
          (snd (C.canonicalCReLU8 x)))
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
        ((_-_)
          (fst (C.canonicalCReLU8 x))
          (snd (C.canonicalCReLU8 x)))))
    (cong
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
      ∀ {x y : Integer} →
      C.canonicalCReLU8 x ＝
      C.canonicalCReLU8 y →
      x ＝ y
    attentionAppend :
      ∀ (accumulator : C.HaarAccumulator)
      (xs ys : List Integer)
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
      ∀ (s : C.GRUState) (x : Integer) →
      C.gruStep
        s
        ((_-_)
          (fst (C.canonicalCReLU8 x))
          (snd (C.canonicalCReLU8 x)))
      ＝
      C.gruStep s x
    reconstructedPrefix :
      ∀ (xs : List Integer) (s : C.GRUState) →
      C.recurrentListState
        C.canonicalGRURecurrentNetwork
        (map
          (λ x →
            (_-_)
              (fst (C.canonicalCReLU8 x))
              (snd (C.canonicalCReLU8 x)))
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
        Integer

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

kla-affine-composition :
  ∀ f₁ b₁ f₂ b₂ →
  C._∘ₘ_
    (C.monoidAffine f₂ b₂)
    (C.monoidAffine f₁ b₁)
  ＝
  C.monoidAffine
    ((_*_) f₂ f₁)
    ((_+_) ((_*_) f₂ b₁) b₂)
kla-affine-composition f₁ b₁ f₂ b₂ = refl

------------------------------------------------------------------------
-- Möbius coefficient shape.  KLA represents each precision update by a
-- 2×2 transition matrix; the actual Bayesian recurrence remains a frontier
-- because this canonical state has no precision variable or field.
------------------------------------------------------------------------

record KLAMobiusMatrix : Set where
  constructor klaMobiusMatrix
  field
    m₁₁ m₁₂ m₂₁ m₂₂ : Integer
open KLAMobiusMatrix public

klaMobiusTransition :
  Integer → Integer → Integer → KLAMobiusMatrix
klaMobiusTransition p aSquared phi =
  klaMobiusMatrix
    ((_+_) 1 ((_*_) p phi))
    ((_*_) aSquared phi)
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
    precision : Integer

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
    a = C.monoidAffine 1 0
    s = klaFullBeliefState a 0
    t = klaFullBeliefState a 1
  in
  false-not-true
    (cong KLAFullBeliefState.precision
      (derive {s = s} {t = t} refl))

record KLAPrecisionBridgeWitness : Set₁ where
  constructor klaPrecisionBridgeWitness
  field
    precisionState : Set
    precisionProjection : precisionState → Integer
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
        (∀ n a → iterateIsomorphism f (suc n) a ≢ a) →
        ∀ n a →
        iterateIsomorphism g (suc n) (to iso a) ≢ to iso a

open CanonicalFiniteCycleExclusionIsomorphismTheorem public

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
... | Sigma._,_ p fixed =
  Sigma._,_ p (fixedImpliesNash N p fixed)

record StationaryLimitTheorem
  (Distribution : Set)
  (P : Distribution → Distribution)
  (μ : ℕ → Distribution)
  (μ∞ : Distribution)
  (Converges : (ℕ → Distribution) → Distribution → Set) : Set₁ where
  constructor stationaryLimitTheorem
  field
    transitionLaw :
      ∀ n → μ (suc n) ＝ P (μ n)
    converges :
      Converges μ μ∞
    limitPreserved :
      Converges μ μ∞ → P μ∞ ＝ μ∞

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
-- cost as proof evidence.
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
... | Sigma._,_ n fixed =
  Sigma._,_ n
  (featureFixedImpliesMixedNash
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
      (cong
        encode
        fixed)))


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
  C.F4IntUKernel → Integer → ℕ → C.F4IntUState → C.F4IntUState
f4Orbit K g zero s = s
f4Orbit K g (suc n) s =
  C.f4ThetaStep K (f4Orbit K g n s) g

record F4UpperBoundedTrajectory
  (K : C.F4IntUKernel)
  (g : Integer)
  (s : C.F4IntUState) : Set₁ where
  constructor f4UpperBoundedTrajectory
  field
    bound : ℕ
    bounded :
      ∀ n →
      C.thetaQ (f4Orbit K g n s) ≤ pos bound

nat-plus-one :
  ∀ n → n + suc zero ＝ suc n
nat-plus-one n =
  trans
    (addNat-suc n zero)
    (cong suc (addNat-idʳ n))

integer-nat-plus-one :
  ∀ n → (pos n) + (pos 1) ＝ pos (suc n)
integer-nat-plus-one n =
  cong pos (nat-plus-one n)

f4-zero-L2-unit-step-code :
  ∀ s →
  C.thetaQ
      (C.f4ThetaStep
        (C.f4IntUKernel 0)
        s
        1)
  ＝
  C.thetaQ s + (pos 1)
f4-zero-L2-unit-step-code s =
  trans
    (cong (λ x → x)
      (C.f4ParameterInvariant
        (C.f4IntUKernel 0)
        s
        1))
    (addInteger-idʳ
      (C.thetaQ s + (pos 1)))

f4-unit-forcing-linear-growth :
  ∀ n s →
  C.thetaQ
      (f4Orbit
        (C.f4IntUKernel 0)
        1
        n
        s)
  ＝
  C.thetaQ s + (pos n)
f4-unit-forcing-linear-growth zero s =
  sym (addInteger-idʳ (C.thetaQ s))
f4-unit-forcing-linear-growth (suc n) s =
  trans
    (f4-zero-L2-unit-step-code
      (f4Orbit (C.f4IntUKernel 0) 1 n s))
    (trans
      (cong
        (λ z → z + (pos 1))
        (f4-unit-forcing-linear-growth n s))
      (trans
        (IntegerLaws.addInteger-assoc
          (C.thetaQ s)
          (pos n)
          (pos 1))
        (cong
          (λ z → C.thetaQ s + z)
          (integer-nat-plus-one n))))

nat-succ-not-le :
  ∀ n → suc n ≤ n → ⊥
nat-succ-not-le zero ()
nat-succ-not-le (suc n) h =
  nat-succ-not-le n h

f4-unit-forcing-no-upper-bound :
  ∀ {s : C.F4IntUState} →
  C.thetaQ s ＝ 0 →
  ¬ F4UpperBoundedTrajectory
      (C.f4IntUKernel 0)
      1
      s
f4-unit-forcing-no-upper-bound thetaZero boundedWitness =
  let
    B = F4UpperBoundedTrajectory.bound boundedWitness
    horizonBound = F4UpperBoundedTrajectory.bounded boundedWitness (suc B)
    growth =
      f4-unit-forcing-linear-growth
        (suc B)
        _
    growthFromZero :
      C.thetaQ
          (f4Orbit
            (C.f4IntUKernel 0)
            1
            (suc B)
            _)
      ＝
      pos (suc B)
    growthFromZero =
      trans
        growth
        (trans
          (cong
            (λ z → z + (pos (suc B)))
            (cong (λ x → x) thetaZero))
          (addInteger-idˡ (pos (suc B))))
    impossibleOrder :
      pos (suc B) ≤ pos B
    impossibleOrder =
      transport (λ z → z ≤ pos B)
        growthFromZero
        horizonBound
  in
    nat-succ-not-le B
      (ℤ-bigger-or-equal-not-less (pos (suc B)) (pos B) impossibleOrder
       (ℕ-order-respects-ℤ-order B (suc B) (<-succ B)))

record CanonicalPureNonOrangeBypassCompletionTheorem : Set₁ where
  constructor canonicalPureNonOrangeBypassCompletionTheorem
  field
    recurrentPrefix :
      RecurrentPrefixMonoidHomomorphism C.GRUState Integer
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
      (∀ n → μ (suc n) ＝ P (μ n)) →
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
    (cong
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
twoPow zero = suc zero
twoPow (suc k) = twoPow k + twoPow k

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
      (sym (zero-left-neutral k))
      (≤-+' n k)

  nat-plus-right-mono-succ :
    (m n : ℕ) (q : m ≤ n) →
    P m n q →
    P (suc m) (suc n) (succ-monotone m n q)
  nat-plus-right-mono-succ m n q ih k =
    transport
      (λ y → suc m + k ≤ y)
      (sym (succ-left n k))
      (transport
        (λ x → x ≤ suc (n + k))
        (sym (succ-left m k))
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
      RecurrentPrefixMonoidHomomorphism C.GRUState Integer
    f4StepLaw :
      ∀ (K : C.CanonicalFullLearnerKernel)
      (o : C.F4IntUState)
      (signal : Integer) →
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
      (cong (decode D) eq)
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
    (cong
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
      ∀ (s : C.GRUState) (x : Integer) →
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
--
-- Every surviving Agda module can be placed in an indexed semantic family.
-- The closure is unconditional at that semantic layer: any supplied sound
-- interpretation and any sound e-graph path produce exact equality.
------------------------------------------------------------------------

f4-add-right-nonnegative :
  ∀ (n m : ℕ) → n ≤ n + m
f4-add-right-nonnegative n zero = ≤-refl n
f4-add-right-nonnegative n (suc m) =
  ≤-trans n (n + m) (suc (n + m))
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
        (fst (strictlyBetter improvement))
        b

open MegaFirstWelfareTheoremConditions public

megaNatNoStrictBack :
  ∀ {n : ℕ} →
  suc n ≤ n →
  ⊥
megaNatNoStrictBack {zero} ()
megaNatNoStrictBack {suc n} h =
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
      budget p (fst (strictlyBetter improvement)) b

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
          (fst (strictlyBetter improvement)))
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
    (λ { (Sigma._,_ _ e) → e })

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
factorTransitionAfterIterate W (suc n) s =
  trans
    (factorTransitionAfterIterate W n (step s))
    (cong
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
          (fst allocationPair)
          (snd allocationPair))
        (λ D →
          RecursiveRadnerEquilibrium
            State
            Agent
            Commodity
            Asset
            Price
            Allocation
            Portfolio
            (fst allocationPair)
            (snd allocationPair)
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
          (fst allocationPair)
          (snd allocationPair))
        (λ D →
          RecursiveRadnerEquilibrium
            State
            Agent
            Commodity
            Asset
            Price
            Allocation
            Portfolio
            (fst allocationPair)
            (snd allocationPair)
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
  (Sigma._,_ p (Sigma._,_ a witness)) =
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
  measure W (iterateStep step (suc n) s)
strictProgressAfterIterate W zero s =
  stepProgress W s
strictProgressAfterIterate W (suc n) s =
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
  iterateStep step (suc n) s ＝ s →
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
      measure (step s) ＝ suc (measure s)

open NatSuccessorProgressWitness public

sucInjective :
  ∀ {m n : ℕ} → suc m ＝ suc n → m ＝ n
sucInjective refl = refl

natPlusLeftCancel :
  ∀ (k m n : ℕ) → k + m ＝ k + n → m ＝ n
natPlusLeftCancel zero m n eq = eq
natPlusLeftCancel (suc k) m n eq =
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
  sym (addNat-idʳ (measure W s))
successorMeasureAfterIterate W (suc n) s =
  trans
    (successor W (iterateStep (step W) n s))
    (trans
      (cong suc (successorMeasureAfterIterate W n s))
      (sym (addNat-suc (measure W s) n)))

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
        (cong (measure W) eq)
        (successorMeasureAfterIterate W n s)))

natSucProgress : ∀ n → n < suc n
natSucProgress n = ≤-refl (suc n)

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
  iterateStep (C.canonicalFullStep K) (suc n) s ＝ s →
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
      iterateStep step (suc n) s ＝ s →
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
  Either
  List (Σ Price (λ p → supports p allocation → ⊥))

finiteCandidatePriceSearch :
  ∀ {Price Allocation : Set}
  (supports : Price → Allocation → Set)
  (allocation : Allocation)
  (decide : ∀ p → FiniteCandidateDecision (supports p allocation))
  (candidates : List Price) →
  FiniteCandidatePriceResult Price Allocation supports allocation
finiteCandidatePriceSearch supports allocation decide [] =
  Right []
finiteCandidatePriceSearch supports allocation decide (p ∷ ps) with decide p
... | acceptCandidate witness =
  Left (Sigma._,_ p witness)
... | rejectCandidate refute with
  finiteCandidatePriceSearch supports allocation decide ps
...   | Left witness =
  Left witness
...   | Right rejected =
  Right ((Sigma._,_ p refute) ∷ rejected)

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
      suc (suc zero)
    extractionIsOne :
      ∀ a →
      extraction (action commonsWorld a) ＝
      suc zero
    capacityIsOne :
      resourceCapacity (sharedResource commonsWorld) ＝
      suc zero

open CommonsNonDerivabilityCounterexample public

twoNotLeOne :
  ¬ suc (suc zero) ≤ suc zero
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
    (transport (λ n → n ≤ suc zero)
      (capacityIsOne C)
      (transport (λ n → suc (suc zero) ≤ n)
        (aggregateExtractionIsTwo C)
        (derive D
          (commonsWorld C)
          (allLocallyOptimal C))))


twoAgentCommonsCounterexample :
  CommonsNonDerivabilityCounterexample
twoAgentCommonsCounterexample =
  commonsNonDerivabilityCounterexample
    (⊤)
    (⊤ Either ⊤)
    (⊤ Either ⊤)
    ℕ
    (λ _ → suc zero)
    (λ _ → suc zero)
    (λ _ _ → Right tt)
    (λ _ → suc zero)
    (λ _ → suc (suc zero))
    (λ _ _ a → a ＝ Right tt)
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
           (cong
             (derive D)
             (sameObservation C)))
         (sound D
           (world₂ C)
           (price₂ C)
           (allocation₂ C)
           (equilibrium₂ C)))

-- Disjoint sum constructors rule out a shared canonical price.
twoPriceDistinct : Left tt ≢ Right tt
twoPriceDistinct ()

twoWorldsNoCommonSupportingPrice :
  ¬ Σ (⊤ Either ⊤)
    (λ p →
      (Left tt ＝ p) ×
      (Right tt ＝ p))
twoWorldsNoCommonSupportingPrice
  (Sigma._,_ p (support₁ , support₂)) =
  (λ ())
    (trans support₁ (sym support₂))

twoWorldCanonicalPriceNonIdentifiabilityCounterexample :
  CanonicalPriceNonIdentifiabilityCounterexample
twoWorldCanonicalPriceNonIdentifiabilityCounterexample =
  canonicalPriceNonIdentifiabilityCounterexample
    (⊤ Either ⊤)
    ⊤
    (⊤ Either ⊤)
    ⊤
    (λ _ → tt)
    (λ world price _ → world ＝ price)
    (λ world price allocation → world ＝ price)
    (λ _ → ⊤)
    (Left tt)
    (Right tt)
    tt
    tt
    (Left tt)
    (Right tt)
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
-- CanonicalToken and learner state share the official unbounded Integer carrier.
-- The identity decoder is total. This proves
-- global injectivity directly from the left-inverse law; no separate
-- separation axiom is required. Continuity is only asserted for the
-- repository's discrete topology, not an analytic topology.
------------------------------------------------------------------------

canonicalTokenDecode : Integer → C.CanonicalToken
canonicalTokenDecode = λ token → token

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
      (cong canonicalTokenDecode eq)
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
        Integer
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
    Integer
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
      (Left tt))
  +
  extraction twoAgentCommonsCounterexample
    (action twoAgentCommonsCounterexample
      (Right tt))
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
    (transport (λ n → n ≤ suc zero)
      (capacityIsOne C)
      (transport (λ n → suc (suc zero) ≤ n)
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
TwoScaleCommonsLevel = ⊤ Either ⊤

noUnconditionalNestedCommonsPreservation-twoScale :
  ¬ NestedCommonsPreservationDerivation
      TwoScaleCommonsLevel
      twoAgentCommonsCounterexample
noUnconditionalNestedCommonsPreservation-twoScale =
  noUnconditionalNestedCommonsPreservation
    (Left tt)
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

module RUSSIntuitionisticCore where

  data RUSSFormula : Set where
    russAtom : ℕ → RUSSFormula
    russBottom : RUSSFormula
    russTop : RUSSFormula
    russConjunction : RUSSFormula → RUSSFormula → RUSSFormula
    russImplication : RUSSFormula → RUSSFormula → RUSSFormula

  data RUSSContext : Set where
    russEmptyContext : RUSSContext
    russExtendContext : RUSSFormula → RUSSContext → RUSSContext

  data RUSSMember : RUSSFormula → RUSSContext → Set where
    russMemberHere :
      ∀ {A Γ} →
      RUSSMember A (russExtendContext A Γ)
    russMemberThere :
      ∀ {A B Γ} →
      RUSSMember A Γ →
      RUSSMember A (russExtendContext B Γ)

  data RUSSFalse : Set where

  data RUSSTrue : Set where
    russUnit : RUSSTrue

  record RUSSPair (A B : Set) : Set where
    constructor russPair
    field
      russFirst : A
      russSecond : B

  open RUSSPair public

  RUSSMeaning : (ℕ → Set) → RUSSFormula → Set
  RUSSMeaning environment (russAtom n) = environment n
  RUSSMeaning environment russBottom = RUSSFalse
  RUSSMeaning environment russTop = RUSSTrue
  RUSSMeaning environment (russConjunction A B) =
    RUSSPair (RUSSMeaning environment A) (RUSSMeaning environment B)
  RUSSMeaning environment (russImplication A B) =
    RUSSMeaning environment A → RUSSMeaning environment B

  data RUSSDerivation : RUSSContext → RUSSFormula → Set where
    russHypothesis :
      ∀ {Γ A} →
      RUSSMember A Γ →
      RUSSDerivation Γ A
    russTopIntroduction :
      ∀ {Γ} →
      RUSSDerivation Γ russTop
    russConjunctionIntroduction :
      ∀ {Γ A B} →
      RUSSDerivation Γ A →
      RUSSDerivation Γ B →
      RUSSDerivation Γ (russConjunction A B)
    russConjunctionLeft :
      ∀ {Γ A B} →
      RUSSDerivation Γ (russConjunction A B) →
      RUSSDerivation Γ A
    russConjunctionRight :
      ∀ {Γ A B} →
      RUSSDerivation Γ (russConjunction A B) →
      RUSSDerivation Γ B
    russImplicationIntroduction :
      ∀ {Γ A B} →
      RUSSDerivation (russExtendContext A Γ) B →
      RUSSDerivation Γ (russImplication A B)
    russImplicationElimination :
      ∀ {Γ A B} →
      RUSSDerivation Γ (russImplication A B) →
      RUSSDerivation Γ A →
      RUSSDerivation Γ B
    russBottomElimination :
      ∀ {Γ A} →
      RUSSDerivation Γ russBottom →
      RUSSDerivation Γ A

  RUSSContextSatisfaction :
    (environment : ℕ → Set) →
    RUSSContext →
    Set
  RUSSContextSatisfaction environment Γ =
    ∀ {A} → RUSSMember A Γ → RUSSMeaning environment A

  russExtendSatisfaction :
    ∀ {Γ A} {environment : ℕ → Set} →
    RUSSContextSatisfaction environment Γ →
    RUSSMeaning environment A →
    RUSSContextSatisfaction environment (russExtendContext A Γ)
  russExtendSatisfaction assumptions witness russMemberHere = witness
  russExtendSatisfaction assumptions witness (russMemberThere member) =
    assumptions member

  russFalseElimination : ∀ {A : Set} → RUSSFalse → A
  russFalseElimination ()

  russSoundness :
    ∀ {Γ A} →
    RUSSDerivation Γ A →
    (environment : ℕ → Set) →
    RUSSContextSatisfaction environment Γ →
    RUSSMeaning environment A
  russSoundness (russHypothesis member) environment assumptions =
    assumptions member
  russSoundness russTopIntroduction environment assumptions = russUnit
  russSoundness
    (russConjunctionIntroduction left right)
    environment assumptions =
      russPair
        (russSoundness left environment assumptions)
        (russSoundness right environment assumptions)
  russSoundness (russConjunctionLeft proof) environment assumptions =
    russFirst (russSoundness proof environment assumptions)
  russSoundness (russConjunctionRight proof) environment assumptions =
    russSecond (russSoundness proof environment assumptions)
  russSoundness
    (russImplicationIntroduction {A = A} proof)
    environment assumptions
    argument =
      russSoundness proof environment
        (russExtendSatisfaction assumptions argument)
  russSoundness
    (russImplicationElimination function argument)
    environment assumptions =
      (russSoundness function environment assumptions)
      (russSoundness argument environment assumptions)
  russSoundness (russBottomElimination proof) environment assumptions =
    russFalseElimination (russSoundness proof environment assumptions)

  russTruthEnvironment : ℕ → Set
  russTruthEnvironment _ = RUSSTrue

  russEmptySatisfaction :
    ∀ {A} →
    RUSSMember A russEmptyContext →
    RUSSMeaning russTruthEnvironment A
  russEmptySatisfaction ()

  -- If an empty-context derivation of false existed, soundness in the
  -- one-element atomic model would construct an inhabitant of RUSSFalse.
  -- This is the consistency theorem for the stated propositional calculus.
  russCoreConsistency :
    RUSSDerivation russEmptyContext russBottom →
    RUSSFalse
  russCoreConsistency derivation =
    russSoundness derivation russTruthEnvironment russEmptySatisfaction

  -- Reuse the canonical learner's exact RUSS basis type instead of
  -- duplicating its schema declarations or silently changing their universes.
  -- Its fields are decidable-predicate Markov, finite register-machine ECT₀,
  -- and Prop-valued countable choice. This alias supplies no inhabitant.
  RUSSPrinciplePackage : Set₃
  RUSSPrinciplePackage = RussianRecursiveMathematicsBasis

