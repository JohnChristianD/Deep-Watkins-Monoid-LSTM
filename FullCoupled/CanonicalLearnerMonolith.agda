{-# OPTIONS
--sized-types
--no-postfix-projections
--no-projection-like
--erased-matches
--prop
--confluence-check
--two-level
--rewriting
--lossy-unification
--experimental-lazy-instances
--backtracking-instance-search
--polarity
--large-indices
--no-forced-argument-recursion
--with-K
--no-guardedness
--injective-type-constructors
#-}

------------------------------------------------------------------------
-- Canonical learner semantics.
--
-- This module is the executable/type-level source of the coupled learner:
-- recurrent monoid-LSTM state, Watkins state, custom q-projected sign-IDBD w/ coupled L2 optimizer state,
-- LCB counts, sparse policy readout, q-log state, the persistent learner channels, and the
-- endogenous feedback signal. The definitions below determine what the
-- learner actually does; theorem modules consume these definitions.
--
-- The main emergent facts are structural: LCB totalCount advances exactly
-- by one per canonical step, the optimizer state is explicit, the policy is
-- invariant under optimizer replacement, and the recurrent
-- components are exposed as composable monoid-LSTM state transitions. The integer
-- token layer and Haar-featured linear transformer are exact formal substrates, not
-- empirical language-model or physical-realism claims.
--
-- This file intentionally contains definitions and local definitional laws,
-- not economic existence conclusions. Convergence, fixed points, market
-- clearing, supporting prices, and Walrasian existence require independent
-- hypotheses and belong to the theorem/economic boundary documented outside
-- this module.
------------------------------------------------------------------------

module FullCoupled.CanonicalLearnerMonolith where

-- Merged external import surface; internal FullCoupled imports remain module-local.
-- Keep imported generic binders out of scope so the canonical module's
-- explicit variable block owns its identifiers without namespace clashes.
open import Haskell.Prelude public hiding (b; f)
open import Haskell.Law public hiding (trustMe)
open import Haskell.Law.Ord.Ordering public
open import Haskell.Law.Equality public hiding (trustMe)
open import Haskell.Law.Functor.FromMonad public
open import Haskell.Law.Semigroup.List public
open import Haskell.Law.Nat public
open import Haskell.Law.Monad.List public
open import Haskell.Law.Monoid.List public
open import Haskell.Prim.Absurd public
open import Haskell.Prim.Applicative public
open import Haskell.Extra.Delay public
open import Haskell.Extra.Erase public
open import Haskell.Extra.Refinement public
open import Haskell.Control.Exception public
open import Agda.Primitive using (Level)
open import Agda.Builtin.Equality.Rewrite public
open import Agda.Builtin.Size public

------------------------------------------------------------------------
-- Shared constructive-computability assumptions and interfaces.
--
-- These live beside the canonical type-level/computational foundations and
-- are re-exported by the theorem monolith. Each principle stays named and
-- conditional: no blanket equivalence between the underlying foundations.
------------------------------------------------------------------------

module ConstructiveComputabilityPostulates where
  -- Markov's principle below is restricted to decidable predicates. There is
  -- no excluded-middle axiom in this module. The outer monolith's Prop-valued
  -- observational equality/rewrite rules remain limited extensionality; no
  -- identity-level function-extensionality postulate is added.
  open import Haskell.Prelude using (Nat; zero; suc; Bool; True; False; List; []; _∷_; _≡_; refl)

  data EmptyComputability : Set where

  Neg : Set → Set
  Neg A = A → EmptyComputability

  data Decidable (A : Set) : Set where
    yes : A → Decidable A
    no : Neg A → Decidable A

  record SigmaWitness (A : Set) (P : A → Set) : Set where
    constructor sigma-witness
    field
      sigmaValue : A
      sigmaEvidence : P sigmaValue

  open SigmaWitness public

  -- Church-encoded existential over propositions. Quantifying over Prop
  -- places this encoding in Prop₁; elimination remains proposition-valued
  -- and does not turn erased evidence into a Set witness.
  PropExists : {A : Set} → (A → Prop) → Prop₁
  PropExists {A} P = (R : Prop) → ((x : A) → P x → R) → R

  propExistsIntro :
    {A : Set} {P : A → Prop} →
    (x : A) → P x → PropExists P
  propExistsIntro x evidence R eliminate = eliminate x evidence

  ----------------------------------------------------------------------
  -- A concrete computation relation for Church's Thesis.
  --
  -- Programs are finite register-machine listings with increment,
  -- decrement/zero-test, jumps, and halt. A computation is a finite trace
  -- ending at halt with the output in register zero. Church's Thesis below
  -- asserts that every total Nat -> Nat function has such a program.
  ----------------------------------------------------------------------

  data RecursiveInstruction : Set where
    haltInstruction : RecursiveInstruction
    incrementRegister : Nat → Nat → RecursiveInstruction
    decrementOrJump : Nat → Nat → Nat → RecursiveInstruction

  RecursiveProgram : Set
  RecursiveProgram = List RecursiveInstruction

  natEquality : Nat → Nat → Bool
  natEquality zero zero = True
  natEquality zero (suc _) = False
  natEquality (suc _) zero = False
  natEquality (suc n) (suc m) = natEquality n m

  updateRegister :
    Nat → Nat → (Nat → Nat) → Nat → Nat
  updateRegister target value registers index with natEquality index target
  ... | True = value
  ... | False = registers index

  initialRegisters : Nat → Nat → Nat
  initialRegisters input index with natEquality index zero
  ... | True = input
  ... | False = zero

  lookupInstruction : RecursiveProgram → Nat → RecursiveInstruction
  lookupInstruction [] _ = haltInstruction
  lookupInstruction (instruction ∷ rest) zero = instruction
  lookupInstruction (_ ∷ rest) (suc pc) = lookupInstruction rest pc

  record MachineConfiguration : Set where
    constructor machineConfiguration
    field
      programCounter : Nat
      registerContents : Nat → Nat

  open MachineConfiguration public

  initialConfiguration : Nat → MachineConfiguration
  initialConfiguration input =
    machineConfiguration zero (initialRegisters input)

  data MachineStep
    (program : RecursiveProgram) :
    MachineConfiguration → MachineConfiguration → Set where
    incrementStep :
      {pc register target : Nat} {store : Nat → Nat} →
      lookupInstruction program pc ≡ incrementRegister register target →
      MachineStep program
        (machineConfiguration pc store)
        (machineConfiguration target
          (updateRegister register (suc (store register)) store))

    decrementZeroStep :
      {pc register onZero onPositive : Nat} {store : Nat → Nat} →
      lookupInstruction program pc ≡
        decrementOrJump register onZero onPositive →
      store register ≡ zero →
      MachineStep program
        (machineConfiguration pc store)
        (machineConfiguration onZero store)

    decrementPositiveStep :
      {pc register onZero onPositive value : Nat}
      {store : Nat → Nat} →
      lookupInstruction program pc ≡
        decrementOrJump register onZero onPositive →
      store register ≡ suc value →
      MachineStep program
        (machineConfiguration pc store)
        (machineConfiguration onPositive
          (updateRegister register value store))

  data MachineSteps (program : RecursiveProgram) :
    MachineConfiguration → MachineConfiguration → Set where
    machineStepsRefl :
      {configuration : MachineConfiguration} →
      MachineSteps program configuration configuration
    machineStepsCons :
      {first middle last : MachineConfiguration} →
      MachineStep program first middle →
      MachineSteps program middle last →
      MachineSteps program first last

  data MachineHalted
    (program : RecursiveProgram) :
    MachineConfiguration → Set where
    machineHalted :
      {pc : Nat} {store : Nat → Nat} →
      lookupInstruction program pc ≡ haltInstruction →
      MachineHalted program (machineConfiguration pc store)

  record ComputationTrace
    (program : RecursiveProgram) (input output : Nat) : Set where
    constructor computationTrace
    field
      finalMachineState : MachineConfiguration
      machineTrace :
        MachineSteps program
          (initialConfiguration input) finalMachineState
      machineTraceHalted : MachineHalted program finalMachineState
      machineTraceOutput :
        registerContents finalMachineState zero ≡ output

  record ComputesFunction
    (program : RecursiveProgram) (f : Nat → Nat) : Set where
    field
      computationFor : (input : Nat) → ComputationTrace program input (f input)

  record ComputesRelation
    (program : RecursiveProgram)
    (relation : Nat → Nat → Set) : Set where
    field
      computesRelatedOutput :
        (input : Nat) →
        SigmaWitness Nat
          (λ output →
            SigmaWitness
              (ComputationTrace program input output)
              (λ _ → relation input output))

  ----------------------------------------------------------------------
  -- First-order Heyting arithmetic syntax and its derivation rules.
  --
  -- This is an object language inside Agda, not an extra host-level axiom.
  -- Quantifiers use named variables; substitution respects shadowing.
  -- The computation atom denotes the arithmetic T-relation for finite
  -- machine traces. Its representation theorem connecting numeric codes
  -- to the register-machine trace below remains a separate proof obligation.
  ----------------------------------------------------------------------

  data HATerm : Set where
    haVariable : Nat → HATerm
    haZeroTerm : HATerm
    haSuccessorTerm : HATerm → HATerm
    haAdditionTerm : HATerm → HATerm → HATerm
    haMultiplicationTerm : HATerm → HATerm → HATerm

  data HAFormula : Set where
    haFalsehood : HAFormula
    haEquality : HATerm → HATerm → HAFormula
    haLessOrEqual : HATerm → HATerm → HAFormula
    haConjunction : HAFormula → HAFormula → HAFormula
    haDisjunction : HAFormula → HAFormula → HAFormula
    haImplication : HAFormula → HAFormula → HAFormula
    haUniversal : Nat → HAFormula → HAFormula
    haExistential : Nat → HAFormula → HAFormula
    haBoundedUniversal : Nat → HATerm → HAFormula → HAFormula
    haBoundedExistential : Nat → HATerm → HAFormula → HAFormula
    haMachineComputes : HATerm → HATerm → HATerm → HATerm → HAFormula

  ----------------------------------------------------------------------
  -- Structural quotation for the object language and machine programs.
  -- These are first-order syntax codes, not a claimed model of Agda's
  -- primitive Reflection API. That stronger interpretation is a separate
  -- presheaf-model obligation.
  ----------------------------------------------------------------------

  data HAQuotation : Set where
    quotedTerm : HATerm → HAQuotation
    quotedFormula : HAFormula → HAQuotation
    quotedProgram : RecursiveProgram → HAQuotation

  data HAUnquoteResult (A : Set) : Set where
    unquoted : A → HAUnquoteResult A
    notQuotedAtThisType : HAUnquoteResult A

  quoteHATermSyntax : HATerm → HAQuotation
  quoteHATermSyntax = quotedTerm

  quoteHAFormulaSyntax : HAFormula → HAQuotation
  quoteHAFormulaSyntax = quotedFormula

  quoteProgramSyntax : RecursiveProgram → HAQuotation
  quoteProgramSyntax = quotedProgram

  unquoteHATermSyntax : HAQuotation → HAUnquoteResult HATerm
  unquoteHATermSyntax (quotedTerm term) = unquoted term
  unquoteHATermSyntax (quotedFormula _) = notQuotedAtThisType
  unquoteHATermSyntax (quotedProgram _) = notQuotedAtThisType

  unquoteHAFormulaSyntax : HAQuotation → HAUnquoteResult HAFormula
  unquoteHAFormulaSyntax (quotedTerm _) = notQuotedAtThisType
  unquoteHAFormulaSyntax (quotedFormula formula) = unquoted formula
  unquoteHAFormulaSyntax (quotedProgram _) = notQuotedAtThisType

  unquoteProgramSyntax : HAQuotation → HAUnquoteResult RecursiveProgram
  unquoteProgramSyntax (quotedTerm _) = notQuotedAtThisType
  unquoteProgramSyntax (quotedFormula _) = notQuotedAtThisType
  unquoteProgramSyntax (quotedProgram program) = unquoted program

  quoteHATermRoundTrip :
    (term : HATerm) →
    unquoteHATermSyntax (quoteHATermSyntax term) ≡ unquoted term
  quoteHATermRoundTrip term = refl

  quoteHAFormulaRoundTrip :
    (formula : HAFormula) →
    unquoteHAFormulaSyntax (quoteHAFormulaSyntax formula) ≡ unquoted formula
  quoteHAFormulaRoundTrip formula = refl

  quoteProgramRoundTrip :
    (program : RecursiveProgram) →
    unquoteProgramSyntax (quoteProgramSyntax program) ≡ unquoted program
  quoteProgramRoundTrip program = refl

  -- Concrete evaluation remains an inductive relation with explicit traces.
  evaluatesProgram :
    (program : RecursiveProgram) (input output : Nat) → Set
  evaluatesProgram program input output =
    ComputationTrace program input output

  haNegation : HAFormula → HAFormula
  haNegation formula = haImplication formula haFalsehood

  -- Explicit object-language bottom and Markov schema (MP₀).
  haBottom : HAFormula
  haBottom = haFalsehood

  haMarkovPrincipleFormula : Nat → HAFormula → HAFormula
  haMarkovPrincipleFormula varIndex body =
    haImplication
      (haUniversal varIndex (haDisjunction body (haNegation body)))
      (haImplication
        (haNegation (haNegation (haExistential varIndex body)))
        (haExistential varIndex body))

  -- The ECT₀ axiom schema. The T-predicate is represented by the explicit
  -- machine-computation atom; its arithmetisation and soundness bridge are
  -- deliberately separate obligations rather than silently postulated.
  haExtendedChurchThesis0Formula :
    Nat → Nat → Nat → Nat → HAFormula → HAFormula → HAFormula
  haExtendedChurchThesis0Formula input output code trace antecedent consequent =
    haImplication
      (haUniversal input
        (haImplication antecedent (haExistential output consequent)))
      (haExistential code
        (haUniversal input
          (haImplication antecedent
            (haExistential output
              (haExistential trace
                (haConjunction
                  (haMachineComputes
                    (haVariable code)
                    (haVariable input)
                    (haVariable trace)
                    (haVariable output))
                  consequent))))))

  haBooleanOr : Bool → Bool → Bool
  haBooleanOr True _ = True
  haBooleanOr False right = right

  haSubstituteTerm : Nat → HATerm → HATerm → HATerm
  haSubstituteTerm varIndex replacement (haVariable index)
    with natEquality varIndex index
  ... | True = replacement
  ... | False = haVariable index
  haSubstituteTerm varIndex replacement haZeroTerm = haZeroTerm
  haSubstituteTerm varIndex replacement (haSuccessorTerm term) =
    haSuccessorTerm (haSubstituteTerm varIndex replacement term)
  haSubstituteTerm varIndex replacement (haAdditionTerm left right) =
    haAdditionTerm
      (haSubstituteTerm varIndex replacement left)
      (haSubstituteTerm varIndex replacement right)
  haSubstituteTerm varIndex replacement (haMultiplicationTerm left right) =
    haMultiplicationTerm
      (haSubstituteTerm varIndex replacement left)
      (haSubstituteTerm varIndex replacement right)

  haSubstituteFormula : Nat → HATerm → HAFormula → HAFormula
  haSubstituteFormula varIndex replacement haFalsehood = haFalsehood
  haSubstituteFormula varIndex replacement (haEquality left right) =
    haEquality
      (haSubstituteTerm varIndex replacement left)
      (haSubstituteTerm varIndex replacement right)
  haSubstituteFormula varIndex replacement (haLessOrEqual left right) =
    haLessOrEqual
      (haSubstituteTerm varIndex replacement left)
      (haSubstituteTerm varIndex replacement right)
  haSubstituteFormula varIndex replacement (haConjunction left right) =
    haConjunction
      (haSubstituteFormula varIndex replacement left)
      (haSubstituteFormula varIndex replacement right)
  haSubstituteFormula varIndex replacement (haDisjunction left right) =
    haDisjunction
      (haSubstituteFormula varIndex replacement left)
      (haSubstituteFormula varIndex replacement right)
  haSubstituteFormula varIndex replacement (haImplication left right) =
    haImplication
      (haSubstituteFormula varIndex replacement left)
      (haSubstituteFormula varIndex replacement right)
  haSubstituteFormula varIndex replacement (haUniversal binder body)
    with natEquality varIndex binder
  ... | True = haUniversal binder body
  ... | False = haUniversal binder (haSubstituteFormula varIndex replacement body)
  haSubstituteFormula varIndex replacement (haExistential binder body)
    with natEquality varIndex binder
  ... | True = haExistential binder body
  ... | False = haExistential binder (haSubstituteFormula varIndex replacement body)
  haSubstituteFormula varIndex replacement
    (haBoundedUniversal binder bound body)
    with natEquality varIndex binder
  ... | True =
    haBoundedUniversal binder (haSubstituteTerm varIndex replacement bound) body
  ... | False =
    haBoundedUniversal binder
      (haSubstituteTerm varIndex replacement bound)
      (haSubstituteFormula varIndex replacement body)
  haSubstituteFormula varIndex replacement
    (haBoundedExistential binder bound body)
    with natEquality varIndex binder
  ... | True =
    haBoundedExistential binder (haSubstituteTerm varIndex replacement bound) body
  ... | False =
    haBoundedExistential binder
      (haSubstituteTerm varIndex replacement bound)
      (haSubstituteFormula varIndex replacement body)
  haSubstituteFormula varIndex replacement
    (haMachineComputes code input trace output) =
    haMachineComputes
      (haSubstituteTerm varIndex replacement code)
      (haSubstituteTerm varIndex replacement input)
      (haSubstituteTerm varIndex replacement trace)
      (haSubstituteTerm varIndex replacement output)

  haOccursTerm : Nat → HATerm → Bool
  haOccursTerm varIndex (haVariable index) = natEquality varIndex index
  haOccursTerm varIndex haZeroTerm = False
  haOccursTerm varIndex (haSuccessorTerm term) = haOccursTerm varIndex term
  haOccursTerm varIndex (haAdditionTerm left right) =
    haBooleanOr (haOccursTerm varIndex left) (haOccursTerm varIndex right)
  haOccursTerm varIndex (haMultiplicationTerm left right) =
    haBooleanOr (haOccursTerm varIndex left) (haOccursTerm varIndex right)

  haOccursFormula : Nat → HAFormula → Bool
  haOccursFormula varIndex haFalsehood = False
  haOccursFormula varIndex (haEquality left right) =
    haBooleanOr (haOccursTerm varIndex left) (haOccursTerm varIndex right)
  haOccursFormula varIndex (haLessOrEqual left right) =
    haBooleanOr (haOccursTerm varIndex left) (haOccursTerm varIndex right)
  haOccursFormula varIndex (haConjunction left right) =
    haBooleanOr (haOccursFormula varIndex left) (haOccursFormula varIndex right)
  haOccursFormula varIndex (haDisjunction left right) =
    haBooleanOr (haOccursFormula varIndex left) (haOccursFormula varIndex right)
  haOccursFormula varIndex (haImplication left right) =
    haBooleanOr (haOccursFormula varIndex left) (haOccursFormula varIndex right)
  haOccursFormula varIndex (haUniversal binder body)
    with natEquality varIndex binder
  ... | True = False
  ... | False = haOccursFormula varIndex body
  haOccursFormula varIndex (haExistential binder body)
    with natEquality varIndex binder
  ... | True = False
  ... | False = haOccursFormula varIndex body
  haOccursFormula varIndex (haBoundedUniversal binder bound body)
    with natEquality varIndex binder
  ... | True = haOccursTerm varIndex bound
  ... | False =
    haBooleanOr (haOccursTerm varIndex bound) (haOccursFormula varIndex body)
  haOccursFormula varIndex (haBoundedExistential binder bound body)
    with natEquality varIndex binder
  ... | True = haOccursTerm varIndex bound
  ... | False =
    haBooleanOr (haOccursTerm varIndex bound) (haOccursFormula varIndex body)
  haOccursFormula varIndex (haMachineComputes code input trace output) =
    haBooleanOr (haOccursTerm varIndex code)
      (haBooleanOr (haOccursTerm varIndex input)
        (haBooleanOr (haOccursTerm varIndex trace) (haOccursTerm varIndex output)))

  -- Named-varIndex substitution is available only at capture-safe
  -- instances. Instead of silently alpha-renaming, the derivation rules ask
  -- for a decidable freshness check before using substitution.
  haBooleanNot : Bool → Bool
  haBooleanNot True = False
  haBooleanNot False = True

  haBooleanAnd : Bool → Bool → Bool
  haBooleanAnd True True = True
  haBooleanAnd _ _ = False

  haSubstitutionCaptureSafe :
    Nat → HATerm → HAFormula → Bool
  haSubstitutionCaptureSafe varIndex replacement haFalsehood = True
  haSubstitutionCaptureSafe varIndex replacement (haEquality left right) = True
  haSubstitutionCaptureSafe varIndex replacement (haLessOrEqual left right) = True
  haSubstitutionCaptureSafe varIndex replacement (haMachineComputes code input trace output) = True
  haSubstitutionCaptureSafe varIndex replacement (haConjunction left right) =
    haBooleanAnd
      (haSubstitutionCaptureSafe varIndex replacement left)
      (haSubstitutionCaptureSafe varIndex replacement right)
  haSubstitutionCaptureSafe varIndex replacement (haDisjunction left right) =
    haBooleanAnd
      (haSubstitutionCaptureSafe varIndex replacement left)
      (haSubstitutionCaptureSafe varIndex replacement right)
  haSubstitutionCaptureSafe varIndex replacement (haImplication left right) =
    haBooleanAnd
      (haSubstitutionCaptureSafe varIndex replacement left)
      (haSubstitutionCaptureSafe varIndex replacement right)
  haSubstitutionCaptureSafe varIndex replacement (haUniversal binder body)
    with natEquality varIndex binder
  ... | True = True
  ... | False =
    haBooleanAnd
      (haBooleanNot
        (haBooleanAnd
          (haOccursTerm binder replacement)
          (haOccursFormula varIndex body)))
      (haSubstitutionCaptureSafe varIndex replacement body)
  haSubstitutionCaptureSafe varIndex replacement (haExistential binder body)
    with natEquality varIndex binder
  ... | True = True
  ... | False =
    haBooleanAnd
      (haBooleanNot
        (haBooleanAnd
          (haOccursTerm binder replacement)
          (haOccursFormula varIndex body)))
      (haSubstitutionCaptureSafe varIndex replacement body)
  haSubstitutionCaptureSafe varIndex replacement
    (haBoundedUniversal binder bound body)
    with natEquality varIndex binder
  ... | True = True
  ... | False =
    haBooleanAnd
      (haBooleanNot
        (haBooleanAnd
          (haOccursTerm binder replacement)
          (haOccursFormula varIndex body)))
      (haSubstitutionCaptureSafe varIndex replacement body)
  haSubstitutionCaptureSafe varIndex replacement
    (haBoundedExistential binder bound body)
    with natEquality varIndex binder
  ... | True = True
  ... | False =
    haBooleanAnd
      (haBooleanNot
        (haBooleanAnd
          (haOccursTerm binder replacement)
          (haOccursFormula varIndex body)))
      (haSubstitutionCaptureSafe varIndex replacement body)

  data HAInContext (formula : HAFormula) : List HAFormula → Set where
    haHere :
      {context : List HAFormula} →
      HAInContext formula (formula ∷ context)
    haThere :
      {other : HAFormula} {context : List HAFormula} →
      HAInContext formula context →
      HAInContext formula (other ∷ context)

  data HAContextFresh (varIndex : Nat) : List HAFormula → Set where
    haContextFreshNil : HAContextFresh varIndex []
    haContextFreshCons :
      {formula : HAFormula} {context : List HAFormula} →
      haOccursFormula varIndex formula ≡ False →
      HAContextFresh varIndex context →
      HAContextFresh varIndex (formula ∷ context)

  -- Delta-zero formula codes: no unbounded quantifier occurs. The arithmetic
  -- order and machine-trace atoms are intended as primitive-recursive
  -- predicates; bounded quantifiers remain explicitly marked in the syntax.
  data HAIsDeltaZero : HAFormula → Set where
    haDeltaFalsehood : HAIsDeltaZero haFalsehood
    haDeltaEquality :
      (left right : HATerm) →
      HAIsDeltaZero (haEquality left right)
    haDeltaLessOrEqual :
      (left right : HATerm) →
      HAIsDeltaZero (haLessOrEqual left right)
    haDeltaMachineComputes :
      (code input trace output : HATerm) →
      HAIsDeltaZero (haMachineComputes code input trace output)
    haDeltaConjunction :
      {left right : HAFormula} →
      HAIsDeltaZero left → HAIsDeltaZero right →
      HAIsDeltaZero (haConjunction left right)
    haDeltaDisjunction :
      {left right : HAFormula} →
      HAIsDeltaZero left → HAIsDeltaZero right →
      HAIsDeltaZero (haDisjunction left right)
    haDeltaImplication :
      {left right : HAFormula} →
      HAIsDeltaZero left → HAIsDeltaZero right →
      HAIsDeltaZero (haImplication left right)
    haDeltaBoundedUniversal :
      {varIndex : Nat} {bound : HATerm} {body : HAFormula} →
      HAIsDeltaZero body →
      HAIsDeltaZero (haBoundedUniversal varIndex bound body)
    haDeltaBoundedExistential :
      {varIndex : Nat} {bound : HATerm} {body : HAFormula} →
      HAIsDeltaZero body →
      HAIsDeltaZero (haBoundedExistential varIndex bound body)

  -- The ECT_0 domain restriction is explicit: no disjunction and no unbounded
  -- existential is admitted except where its body is delta-zero.
  data HAAlmostNegative : HAFormula → Set where
    haAlmostFalsehood : HAAlmostNegative haFalsehood
    haAlmostEquality :
      (left right : HATerm) → HAAlmostNegative (haEquality left right)
    haAlmostLessOrEqual :
      (left right : HATerm) → HAAlmostNegative (haLessOrEqual left right)
    haAlmostMachineComputes :
      (code input trace output : HATerm) →
      HAAlmostNegative (haMachineComputes code input trace output)
    haAlmostConjunction :
      {left right : HAFormula} →
      HAAlmostNegative left → HAAlmostNegative right →
      HAAlmostNegative (haConjunction left right)
    haAlmostImplication :
      {left right : HAFormula} →
      HAAlmostNegative left → HAAlmostNegative right →
      HAAlmostNegative (haImplication left right)
    haAlmostUniversal :
      {varIndex : Nat} {body : HAFormula} →
      HAAlmostNegative body → HAAlmostNegative (haUniversal varIndex body)
    haAlmostBoundedUniversal :
      {varIndex : Nat} {bound : HATerm} {body : HAFormula} →
      HAAlmostNegative body →
      HAAlmostNegative (haBoundedUniversal varIndex bound body)
    haAlmostExistentialDeltaZero :
      {varIndex : Nat} {body : HAFormula} →
      HAIsDeltaZero body → HAAlmostNegative (haExistential varIndex body)
    haAlmostBoundedExistentialDeltaZero :
      {varIndex : Nat} {bound : HATerm} {body : HAFormula} →
      HAIsDeltaZero body →
      HAAlmostNegative (haBoundedExistential varIndex bound body)

  data HADerivation : List HAFormula → HAFormula → Set where
    haAssumption :
      {context : List HAFormula} {formula : HAFormula} →
      HAInContext formula context → HADerivation context formula
    haFalseElimination :
      {context : List HAFormula} {formula : HAFormula} →
      HADerivation context haFalsehood → HADerivation context formula
    haImplicationIntroduction :
      {context : List HAFormula} {left right : HAFormula} →
      HADerivation (left ∷ context) right →
      HADerivation context (haImplication left right)
    haImplicationElimination :
      {context : List HAFormula} {left right : HAFormula} →
      HADerivation context (haImplication left right) →
      HADerivation context left →
      HADerivation context right
    haConjunctionIntroduction :
      {context : List HAFormula} {left right : HAFormula} →
      HADerivation context left →
      HADerivation context right →
      HADerivation context (haConjunction left right)
    haConjunctionEliminationLeft :
      {context : List HAFormula} {left right : HAFormula} →
      HADerivation context (haConjunction left right) →
      HADerivation context left
    haConjunctionEliminationRight :
      {context : List HAFormula} {left right : HAFormula} →
      HADerivation context (haConjunction left right) →
      HADerivation context right
    haDisjunctionIntroductionLeft :
      {context : List HAFormula} {left right : HAFormula} →
      HADerivation context left →
      HADerivation context (haDisjunction left right)
    haDisjunctionIntroductionRight :
      {context : List HAFormula} {left right : HAFormula} →
      HADerivation context right →
      HADerivation context (haDisjunction left right)
    haDisjunctionElimination :
      {context : List HAFormula} {left right conclusion : HAFormula} →
      HADerivation context (haDisjunction left right) →
      HADerivation (left ∷ context) conclusion →
      HADerivation (right ∷ context) conclusion →
      HADerivation context conclusion
    haUniversalIntroduction :
      {context : List HAFormula} {varIndex : Nat} {body : HAFormula} →
      HAContextFresh varIndex context →
      HADerivation context body →
      HADerivation context (haUniversal varIndex body)
    haUniversalElimination :
      {context : List HAFormula} {varIndex : Nat} {body : HAFormula} →
      HADerivation context (haUniversal varIndex body) →
      (term : HATerm) →
      haSubstitutionCaptureSafe varIndex term body ≡ True →
      HADerivation context (haSubstituteFormula varIndex term body)
    haExistentialIntroduction :
      {context : List HAFormula} {varIndex : Nat} {body : HAFormula} →
      (term : HATerm) →
      haSubstitutionCaptureSafe varIndex term body ≡ True →
      HADerivation context (haSubstituteFormula varIndex term body) →
      HADerivation context (haExistential varIndex body)
    haExistentialElimination :
      {context : List HAFormula} {varIndex : Nat} {body conclusion : HAFormula} →
      HADerivation context (haExistential varIndex body) →
      HADerivation (body ∷ context) conclusion →
      HAContextFresh varIndex context →
      haOccursFormula varIndex conclusion ≡ False →
      HADerivation context conclusion
    haEqualityReflexivity :
      {context : List HAFormula} (term : HATerm) →
      HADerivation context (haEquality term term)
    haEqualitySymmetry :
      {context : List HAFormula} {left right : HATerm} →
      HADerivation context (haEquality left right) →
      HADerivation context (haEquality right left)
    haEqualityTransitivity :
      {context : List HAFormula} {left middle right : HATerm} →
      HADerivation context (haEquality left middle) →
      HADerivation context (haEquality middle right) →
      HADerivation context (haEquality left right)
    haEqualitySubstitution :
      {context : List HAFormula} {varIndex : Nat}
      {formula : HAFormula} {left right : HATerm} →
      HADerivation context (haEquality left right) →
      haSubstitutionCaptureSafe varIndex left formula ≡ True →
      haSubstitutionCaptureSafe varIndex right formula ≡ True →
      HADerivation context (haSubstituteFormula varIndex left formula) →
      HADerivation context (haSubstituteFormula varIndex right formula)
    haZeroNotSuccessor :
      {context : List HAFormula} (term : HATerm) →
      HADerivation context
        (haImplication (haEquality haZeroTerm (haSuccessorTerm term)) haFalsehood)
    haSuccessorNotZero :
      {context : List HAFormula} (term : HATerm) →
      HADerivation context
        (haImplication (haEquality (haSuccessorTerm term) haZeroTerm) haFalsehood)
    haSuccessorInjective :
      {context : List HAFormula} (left right : HATerm) →
      HADerivation context
        (haImplication
          (haEquality (haSuccessorTerm left) (haSuccessorTerm right))
          (haEquality left right))
    haAdditionZero :
      {context : List HAFormula} (term : HATerm) →
      HADerivation context (haEquality (haAdditionTerm term haZeroTerm) term)
    haAdditionSuccessor :
      {context : List HAFormula} (left right : HATerm) →
      HADerivation context
        (haEquality
          (haAdditionTerm left (haSuccessorTerm right))
          (haSuccessorTerm (haAdditionTerm left right)))
    haMultiplicationZero :
      {context : List HAFormula} (term : HATerm) →
      HADerivation context
        (haEquality (haMultiplicationTerm term haZeroTerm) haZeroTerm)
    haMultiplicationSuccessor :
      {context : List HAFormula} (left right : HATerm) →
      HADerivation context
        (haEquality
          (haMultiplicationTerm left (haSuccessorTerm right))
          (haAdditionTerm (haMultiplicationTerm left right) left))
    haInduction :
      {context : List HAFormula} (varIndex : Nat) (body : HAFormula) →
      haSubstitutionCaptureSafe varIndex haZeroTerm body ≡ True →
      haSubstitutionCaptureSafe varIndex (haSuccessorTerm (haVariable varIndex)) body ≡ True →
      HADerivation context (haSubstituteFormula varIndex haZeroTerm body) →
      HADerivation context
        (haUniversal varIndex
          (haImplication body
            (haSubstituteFormula varIndex
              (haSuccessorTerm (haVariable varIndex)) body))) →
      HADerivation context (haUniversal varIndex body)
    haBoundedUniversalIntroduction :
      {context : List HAFormula} {varIndex : Nat}
      {bound : HATerm} {body : HAFormula} →
      haOccursTerm varIndex bound ≡ False →
      HADerivation context
        (haUniversal varIndex
          (haImplication
            (haLessOrEqual (haVariable varIndex) bound) body)) →
      HADerivation context (haBoundedUniversal varIndex bound body)
    haBoundedUniversalElimination :
      {context : List HAFormula} {varIndex : Nat}
      {bound : HATerm} {body : HAFormula} →
      HADerivation context (haBoundedUniversal varIndex bound body) →
      (term : HATerm) →
      haSubstitutionCaptureSafe varIndex term body ≡ True →
      HADerivation context
        (haImplication
          (haLessOrEqual term bound)
          (haSubstituteFormula varIndex term body))
    haBoundedExistentialIntroduction :
      {context : List HAFormula} {varIndex : Nat}
      {bound : HATerm} {body : HAFormula} →
      HADerivation context
        (haExistential varIndex
          (haConjunction
            (haLessOrEqual (haVariable varIndex) bound) body)) →
      HADerivation context (haBoundedExistential varIndex bound body)
    haBoundedExistentialElimination :
      {context : List HAFormula} {varIndex : Nat}
      {bound : HATerm} {body : HAFormula} →
      HADerivation context (haBoundedExistential varIndex bound body) →
      HADerivation context
        (haExistential varIndex
          (haConjunction
            (haLessOrEqual (haVariable varIndex) bound) body))
    haMarkovPrinciple :
      {context : List HAFormula} (varIndex : Nat) {body : HAFormula} →
      HAIsDeltaZero body →
      HADerivation context (haMarkovPrincipleFormula varIndex body)
    haExtendedChurchThesis0 :
      {context : List HAFormula}
      {input output code trace : Nat}
      {antecedent consequent : HAFormula} →
      HAAlmostNegative antecedent →
      HAContextFresh input context →
      HAContextFresh code context →
      HAContextFresh trace context →
      haOccursFormula output antecedent ≡ False →
      haOccursFormula code antecedent ≡ False →
      haOccursFormula trace antecedent ≡ False →
      haOccursFormula code consequent ≡ False →
      haOccursFormula trace consequent ≡ False →
      natEquality input output ≡ False →
      natEquality input code ≡ False →
      natEquality input trace ≡ False →
      natEquality output code ≡ False →
      natEquality output trace ≡ False →
      natEquality code trace ≡ False →
      HADerivation context
        (haExtendedChurchThesis0Formula
          input output code trace antecedent consequent)

  data ConstructiveArithmeticSchema : Set where
    markovPrincipleSchema : ConstructiveArithmeticSchema
    extendedChurchThesis0Schema : ConstructiveArithmeticSchema

  -- An untruncated marker for the object-language ECT_0 schema. Actual
  -- machine-code soundness is not inferred from this marker.
  churchThesisSchema : ConstructiveArithmeticSchema
  churchThesisSchema = extendedChurchThesis0Schema

  ----------------------------------------------------------------------
  -- Russian constructivism: explicit global axiom schemas.
  ----------------------------------------------------------------------

  -- The recursive Russian basis is one explicit, reviewable trust boundary.
  -- Grouping these principles supports uniform downstream use; it proves
  -- neither their joint consistency nor soundness/canonicity of Agda's evaluator.
  -- TRUST BOUNDARY (not a consistency theorem):
  -- This record groups the three explicitly assumed RUSS principles used
  -- by this development: Markov's Principle, the project-specific ECT₀
  -- signature below, and proposition-valued countable choice. The grouping
  -- makes the dependency visible; it neither derives the principles from
  -- MLTT nor proves their joint consistency.
  --
  -- CONSISTENCY STATUS: this module does not certify RUSS consistency.
  -- Type-checking any client only establishes derivability relative to this
  -- postulate, Agda's trusted checker/primitives, rewrite rules, and the full
  -- imported theory. A consistency claim requires a model or relative-
  -- consistency argument interpreting this exact signature and its complete
  -- transitive dependency closure. An empty-type search is not such an argument.
  --
  -- FORMALIZATION BOUNDARY: do not identify the ECT₀ signature below with a
  -- textbook formulation without proving the equivalence of its computation
  -- relation, admissible predicates, and quantifiers. Its computational
  -- content is a substantive axiom here. Do not turn these principles into
  -- REWRITE rules: they are assumptions, not definitional computation rules.
  record RussianRecursiveMathematicsBasis : Set₃ where
    constructor russianRecursiveMathematicsBasis
    field
      russMarkov :
        (P : Nat → Set) →
        ((n : Nat) → Decidable (P n)) →
        Neg (Neg (SigmaWitness Nat P)) →
        SigmaWitness Nat P

      -- Extended Church Thesis 0: a stated assumption for the finite
      -- register-machine relation, not a soundness theorem for the evaluator.
      russECT0 :
        (relation : Nat → Nat → Set) →
        ((input output : Nat) → Decidable (relation input output)) →
        ((input : Nat) → SigmaWitness Nat (relation input)) →
        SigmaWitness RecursiveProgram
          (λ program → ComputesRelation program relation)

      -- Prop-valued countable choice does not compute a choice function
      -- from erased existential evidence.
      russCountableChoice :
        (A : Nat → Set) →
        (P : (n : Nat) → A n → Prop) →
        ((n : Nat) → PropExists (P n)) →
        PropExists {A = (n : Nat) → A n}
          (λ choose → (n : Nat) → P n (choose n))

  -- The sole RUSS trust entry in this interface. The record's projections
  -- below are consequences of this assumption; they are not extra axioms.
  postulate
    russianRecursiveMathematicsAssumptions : RussianRecursiveMathematicsBasis

  -- Keep the established public names as projections from the single basis.
  russianMarkovPrinciple :
    (P : Nat → Set) →
    ((n : Nat) → Decidable (P n)) →
    Neg (Neg (SigmaWitness Nat P)) →
    SigmaWitness Nat P
  russianMarkovPrinciple =
    RussianRecursiveMathematicsBasis.russMarkov russianRecursiveMathematicsAssumptions

  extendedChurchThesis0 :
    (relation : Nat → Nat → Set) →
    ((input output : Nat) → Decidable (relation input output)) →
    ((input : Nat) → SigmaWitness Nat (relation input)) →
    SigmaWitness RecursiveProgram
      (λ program → ComputesRelation program relation)
  extendedChurchThesis0 =
    RussianRecursiveMathematicsBasis.russECT0 russianRecursiveMathematicsAssumptions

  russianCountableChoice :
    (A : Nat → Set) →
    (P : (n : Nat) → A n → Prop) →
    ((n : Nat) → PropExists (P n)) →
    PropExists {A = (n : Nat) → A n}
      (λ choose → (n : Nat) → P n (choose n))
  russianCountableChoice =
    RussianRecursiveMathematicsBasis.russCountableChoice russianRecursiveMathematicsAssumptions

  -- Keep the established identifier, now explicitly referring to ECT_0.
  -- This preserves fully relevant Set-level program and trace witnesses.
  churchThesis :
    (relation : Nat → Nat → Set) →
    ((input output : Nat) → Decidable (relation input output)) →
    ((input : Nat) → SigmaWitness Nat (relation input)) →
    SigmaWitness RecursiveProgram
      (λ program → ComputesRelation program relation)
  churchThesis = extendedChurchThesis0

  ----------------------------------------------------------------------
  -- A data-level version of countable choice is a theorem: if every index
  -- already supplies a computational SigmaWitness, select its projections.
  ----------------------------------------------------------------------

  constructiveCountableChoice :
    (A : Nat → Set) →
    (P : (n : Nat) → A n → Set) →
    ((n : Nat) → SigmaWitness (A n) (P n)) →
    SigmaWitness
      ((n : Nat) → A n)
      (λ choose → (n : Nat) → P n (choose n))
  constructiveCountableChoice A P witnesses =
    sigma-witness
      (λ n → sigmaValue (witnesses n))
      (λ n → sigmaEvidence (witnesses n))

  ----------------------------------------------------------------------
  -- Scott-Ershov effective-domain contract.
  --
  -- The caller supplies a carrier, approximation order, and way-below
  -- relation. Compactness and approximation convergence are assumptions
  -- for this particular domain, not a theorem about every ordered set.
  ----------------------------------------------------------------------

  -- A Scott-Ershov domain is explicit data, not an axiom that every carrier
  -- has a compact basis. The approximation sequence is defined from its
  -- effective index and compact-code enumerator, so its computation is real
  -- definitional reduction rather than a rewrite rule over a record projection.
  record ScottErshovEffectiveDomainData
    (D : Set)
    (_⊑d_ : D → D → Set)
    (_≪d_ : D → D → Set) : Set₁ where
    constructor scottErshovEffectiveDomainData
    field
      compactCode : Nat → D
      compactCodeIsCompact :
        (n : Nat) → _≪d_ (compactCode n) (compactCode n)

      approximationIndex : D → Nat → Nat

      approximationBelow :
        (x : D) (n : Nat) →
        _⊑d_ (compactCode (approximationIndex x n)) x

      approximationIncreasing :
        (x : D) (n : Nat) →
        _⊑d_
          (compactCode (approximationIndex x n))
          (compactCode (approximationIndex x (suc n)))

      approximationLeast :
        (x y : D) →
        ((n : Nat) → _⊑d_ (compactCode (approximationIndex x n)) y) →
        _⊑d_ x y

  module ScottErshovEffectiveDomain
    {D : Set}
    {_⊑d_ : D → D → Set}
    {_≪d_ : D → D → Set}
    (domain : ScottErshovEffectiveDomainData D _⊑d_ _≪d_) where

    compactCode : Nat → D
    compactCode = ScottErshovEffectiveDomainData.compactCode domain

    compactCodeIsCompact :
      (n : Nat) → _≪d_ (compactCode n) (compactCode n)
    compactCodeIsCompact =
      ScottErshovEffectiveDomainData.compactCodeIsCompact domain

    approximationIndex : D → Nat → Nat
    approximationIndex =
      ScottErshovEffectiveDomainData.approximationIndex domain

    compactApproximation : D → Nat → D
    compactApproximation x n = compactCode (approximationIndex x n)

    compactApproximationComputes :
      (x : D) (n : Nat) →
      compactApproximation x n ≡ compactCode (approximationIndex x n)
    compactApproximationComputes x n = refl

    compactApproximationIsCompact :
      (x : D) (n : Nat) →
      _≪d_ (compactApproximation x n) (compactApproximation x n)
    compactApproximationIsCompact x n =
      compactCodeIsCompact (approximationIndex x n)

    compactApproximationBelow :
      (x : D) (n : Nat) →
      _⊑d_ (compactApproximation x n) x
    compactApproximationBelow =
      ScottErshovEffectiveDomainData.approximationBelow domain

    compactApproximationIncreasing :
      (x : D) (n : Nat) →
      _⊑d_ (compactApproximation x n) (compactApproximation x (suc n))
    compactApproximationIncreasing =
      ScottErshovEffectiveDomainData.approximationIncreasing domain

    compactApproximationLeast :
      (x y : D) →
      ((n : Nat) → _⊑d_ (compactApproximation x n) y) →
      _⊑d_ x y
    compactApproximationLeast =
      ScottErshovEffectiveDomainData.approximationLeast domain

  ----------------------------------------------------------------------
  -- Henkin construction with consistency and witness hypotheses explicit.
  -- A result is returned with a concrete model witness and satisfaction
  -- evidence; completeness is not asserted for an unspecified proof system.
  ----------------------------------------------------------------------

  record HenkinTheoryInterface : Set₁ where
    field
      Sentence : Set
      Model : Set
      Consistent : (Sentence → Set) → Set
      HasHenkinWitnesses : (Sentence → Set) → Set
      Satisfies : Model → Sentence → Set

      -- Each logic supplies its own constructive Henkin builder. The mere
      -- labels "consistent" and "has witnesses" are not treated as axioms
      -- from which a model of arbitrary uninterpreted predicates follows.
      henkinModelExists :
        (T : Sentence → Set) →
        Consistent T →
        HasHenkinWitnesses T →
        SigmaWitness
          Model
          (λ M → (φ : Sentence) → T φ → Satisfies M φ)

  open HenkinTheoryInterface public

open ConstructiveComputabilityPostulates public using
  ( RussianRecursiveMathematicsBasis
  ; russianRecursiveMathematicsAssumptions
  ; russianMarkovPrinciple
  ; extendedChurchThesis0
  ; russianCountableChoice
  ; churchThesis
  ; constructiveCountableChoice
  )

variable
  ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
  A B C       : Set ℓ
  P Q         : A → Set ℓ
  x y z       : A
  f g h       : (x : A) → P x
  b b₁ b₂ b₃  : Bool
  k l m n     : Nat
  xs ys zs    : List A

cong : (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

transport : (P : A → Set ℓ) → x ≡ y → P x → P y
transport P refl p = p

+comm : m + n ≡ n + m
+comm {m = zero}  = refl
+comm {m = suc m} = cong suc (+comm {m = m})

zero+ : zero + n ≡ n
zero+ = refl

suc+ : (suc m) + n ≡ suc (m + n)
suc+ = refl

+zero : m + zero ≡ m
+zero {m = zero}  = refl
+zero {m = suc m} = cong suc +zero

+suc : m + (suc n) ≡ suc (m + n)
+suc {m = zero}  = refl
+suc {m = suc m} = cong suc +suc

{-# REWRITE +zero +suc #-}

map : (A → B) → List A → List B
map f []       = []
map f (x ∷ xs) = (f x) ∷ (map f xs)

infixr 5 _++_
_++_ : List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

map-id : map (λ x → x) xs ≡ xs
map-id {xs = []}     = refl
map-id {xs = x ∷ xs} = cong (_∷_ x) map-id

map-fuse : map f (map g xs) ≡ map (λ x → f (g x)) xs
map-fuse {xs = []}     = refl
map-fuse {xs = x ∷ xs} = cong (_∷_ _) map-fuse

map-++ : map f (xs ++ ys) ≡ (map f xs) ++ (map f ys)
map-++ {xs = []}     = refl
map-++ {xs = x ∷ xs} = cong (_∷_ _) (map-++ {xs = xs})

{-# REWRITE map-id map-fuse map-++ #-}

-- Constructive transport over the reflexive-only relation used as the
-- equality substrate for potential quotient interfaces. This kernel lemma
-- has no postulates or rewrite rules; the quotient eliminator itself is not
-- assumed here.
data _≐_ {A : Set ℓ} (x : A) : A → Set ℓ where
  refl≐ : x ≐ x

transportR : (P : A → Set ℓ) → x ≐ y → P x → P y
transportR P refl≐ value = value

transportR-refl :
  (P : A → Set ℓ) (value : P x) →
  transportR P refl≐ value ≡ value
transportR-refl P value = refl




-- Executable exceptions are represented as values, never as inhabitants
-- of arbitrary types. This keeps Haskell-style failure out of the Agda
-- logical universe: there is no postulate of type Exc → A.
module ConstructiveExceptionSemantics where
  open import Haskell.Prelude using (Bool; True; False; _≡_; refl)

  data Exc : Set where
    runtimeException : Exc

  data Exceptional (A : Set) : Set where
    returned : A → Exceptional A
    failed : Exc → Exceptional A

  raise : {A : Set} → Exc → Exceptional A
  raise = failed

  mapExceptional :
    {A B : Set} → (A → B) → Exceptional A → Exceptional B
  mapExceptional f (returned value) = returned (f value)
  mapExceptional _ (failed e) = failed e

  exceptionPropagation :
    {A B : Set} (f : A → B) (e : Exc) →
    mapExceptional f (raise {A = A} e) ≡ raise {A = B} e
  exceptionPropagation f e = refl

  catchExceptionalBool :
    (P : Exceptional Bool → Set) →
    P (returned True) →
    P (returned False) →
    ((e : Exc) → P (failed e)) →
    (b : Exceptional Bool) → P b
  catchExceptionalBool P onTrue onFalse onException (returned True) =
    onTrue
  catchExceptionalBool P onTrue onFalse onException (returned False) =
    onFalse
  catchExceptionalBool P onTrue onFalse onException (failed e) =
    onException e


Int : Set
Int = ℤ

infixl 31 _+Int_
_+Int_ : Int → Int → Int
_+Int_ = _ℤ+_

infixl 31 _*Int_
_*Int_ : Int → Int → Int
_*Int_ = _ℤ*_


cong₂ : ∀ {A B C : Set} (f : A → B → C) {x y : A} {u v : B} → x ＝ y → u ＝ v → f x u ＝ f y v
cong₂ f refl refl = refl

trans : ∀ {A : Set} {x y z : A} → x ＝ y → y ＝ z → x ＝ z
trans refl q = q



record IntCode : Set where
  constructor intCode
  field intCodeValue : Int
open IntCode public

intCodeStateSpace : Set
intCodeStateSpace = Int

zeroIntCode : IntCode
zeroIntCode = intCode (pos 0)

oneIntCode : IntCode
oneIntCode = intCode (pos 1)

intCodeOfNat : ℕ → IntCode
intCodeOfNat n = intCode (pos n)

intCodeAdd : IntCode → IntCode → IntCode
intCodeAdd x y = intCode (intCodeValue x +Int intCodeValue y)

intCodeMul : IntCode → IntCode → IntCode
intCodeMul x y = intCode (intCodeValue x *Int intCodeValue y)

intNeg : Int → Int
intNeg (pos zero) = pos zero
intNeg (pos (succ n)) = negsucc n
intNeg (negsucc n) = pos (succ n)

intCodeNeg : IntCode → IntCode
intCodeNeg x = intCode (intNeg (intCodeValue x))

intCodeSub : IntCode → IntCode → IntCode
intCodeSub x y = intCode (intCodeValue x +Int intCodeValue (intCodeNeg y))

intCode+-assoc : ∀ a b c → intCodeAdd (intCodeAdd a b) c ＝ intCodeAdd a (intCodeAdd b c)
intCode+-assoc a b c = ap intCode (ℤ+-assoc (intCodeValue a) (intCodeValue b) (intCodeValue c))

intCode*-assoc : ∀ a b c → intCodeMul (intCodeMul a b) c ＝ intCodeMul a (intCodeMul b c)
intCode*-assoc a b c = ap intCode (ℤ*-assoc (intCodeValue a) (intCodeValue b) (intCodeValue c))

sym : ∀ {A : Set} {x y : A} → x ＝ y → y ＝ x
sym refl = refl

intCode*-distribˡ : ∀ a b c → intCodeMul a (intCodeAdd b c) ＝ intCodeAdd (intCodeMul a b) (intCodeMul a c)
intCode*-distribˡ a b c =
  ap intCode (distributivity-mult-over-ℤ' (intCodeValue b) (intCodeValue c) (intCodeValue a))

intCode*-idˡ : ∀ a → intCodeMul oneIntCode a ＝ a
intCode*-idˡ a = ap intCode (ℤ-mult-left-id (intCodeValue a))

intCode*-idʳ : ∀ a → intCodeMul a oneIntCode ＝ a
intCode*-idʳ a = ap intCode (ℤ-mult-right-id (intCodeValue a))

intCode*-zeroʳ : ∀ a → intCodeMul a zeroIntCode ＝ zeroIntCode
intCode*-zeroʳ a = ap intCode (ℤ-zero-right-is-zero (intCodeValue a))

intCode*-zeroˡ : ∀ a → intCodeMul zeroIntCode a ＝ zeroIntCode
intCode*-zeroˡ a = ap intCode (ℤ-zero-left-base (intCodeValue a))

intCode+-idˡ : ∀ a → intCodeAdd zeroIntCode a ＝ a
intCode+-idˡ a = ap intCode (ℤ-zero-left-neutral (intCodeValue a))

intCode+-idʳ : ∀ a → intCodeAdd a zeroIntCode ＝ a
intCode+-idʳ a = ap intCode (ℤ-zero-right-neutral (intCodeValue a))

intCodeRoundtrip : ∀ n → intCodeValue (intCodeOfNat n) ＝ pos n
intCodeRoundtrip n = refl



plus-zero : ∀ n → n + zero ＝ n
plus-zero zero = refl
plus-zero (succ n) = ap succ (plus-zero n)

plus-succ : ∀ (m n : ℕ) → m + succ n ＝ succ (m + n)
plus-succ zero n = refl
plus-succ (succ m) n = refl

plus-succ-lt : ∀ (m n : ℕ) → m <ℕ (m + succ n)
plus-succ-lt m zero = ≤-refl (succ m)
plus-succ-lt m (succ n) = ≤-+ m (succ n)

plus-succ-not-self : ∀ (m n : ℕ) → m + succ n ≠ m
plus-succ-not-self m n eq =
  not-less-than-itself m (transport (λ z → m <ℕ z) eq (plus-succ-lt m n))

succ-succ-lt : ∀ (n : ℕ) → n <ℕ succ (succ n)
succ-succ-lt zero = ≤-succ zero
succ-succ-lt (succ n) = ≤-succ (succ n)

succ-succ-not-self : ∀ n → succ (succ n) ≠ n
succ-succ-not-self n eq =
  not-less-than-itself (succ (succ n))
    (transport (λ z → z <ℕ succ (succ n)) (eq ⁻¹) (succ-succ-lt n))

iterate : ∀ {S : Set} → (S → S) → ℕ → S → S
iterate step zero s = s
iterate step (succ n) s = step (iterate step n s)

OrbitNonFixed : ∀ {S : Set} {step : S → S} → S → Set
OrbitNonFixed {step = step} s = ∀ n → iterate step n s ≠ step (iterate step n s)

data Signed : Set where
  signedNeg : ℕ → Signed
  signedZer : Signed
  signedPos : ℕ → Signed

signedCode : IntCode → Signed
signedCode (intCode (pos 0)) = signedZer
signedCode (intCode (pos (succ n))) = signedPos (succ n)
signedCode (intCode (negsucc n)) = signedNeg (succ n)

data BoolLike : Set where
  enabled disabled : BoolLike

record ActionSpace (A : Set) : Set where
  constructor actionSpace
  field
    candidates : List ℕ
    witness : ℕ
open ActionSpace public

QFunction : ∀ {A : Set} → Set
QFunction {A} = ℕ → IntCode

CountFunction : ∀ {A : Set} → Set
CountFunction {A} = ℕ → ℕ

zeroQ : ∀ {A : Set} → QFunction {A}
zeroQ _ = zeroIntCode

zeroCounts : ∀ {A : Set} → CountFunction {A}
zeroCounts _ = zero

natEq : ℕ → ℕ → BoolLike
natEq zero zero = enabled
natEq zero (succ n) = disabled
natEq (succ m) zero = disabled
natEq (succ m) (succ n) = natEq m n

natLt : ℕ → ℕ → BoolLike
natLt zero zero = disabled
natLt zero (succ n) = enabled
natLt (succ m) zero = disabled
natLt (succ m) (succ n) = natLt m n

natLE : ℕ → ℕ → BoolLike
natLE zero n = enabled
natLE (succ m) zero = disabled
natLE (succ m) (succ n) = natLE m n

maxNat : ℕ → ℕ → ℕ
maxNat zero n = n
maxNat (succ m) zero = succ m
maxNat (succ m) (succ n) = succ (maxNat m n)

updateAt : ∀ {A : Set} → QFunction {A} → ℕ → IntCode → QFunction {A}
updateAt q a r i with natEq i a
... | enabled = intCodeAdd (q i) r
... | disabled = q i

incAt : ∀ {A : Set} → CountFunction {A} → ℕ → CountFunction {A}
incAt c a i with natEq i a
... | enabled = succ (c i)
... | disabled = c i

record CriticState (A : Set) : Set where
  constructor criticState
  field values : QFunction {A}
open CriticState public

record WatkinsKernel (A : Set) : Set₁ where
  constructor mkWatkinsKernel
  field
    updateCritic : CriticState A → IntCode → CriticState A
    greedy : CriticState A → IntCode → BoolLike
    traceUpdate : BoolLike → BoolLike → BoolLike
open WatkinsKernel public

record WatkinsState (A : Set) : Set where
  constructor watkinsState
  field critic : CriticState A
        signal : IntCode
        trace : BoolLike
open WatkinsState public

watkinsStep : ∀ {A : Set} → WatkinsKernel A → WatkinsState A → WatkinsState A
watkinsStep K s = watkinsState
  (updateCritic K (critic s) (signal s))
  (signal s)
  (traceUpdate K (trace s) (greedy K (critic s) (signal s)))

record LCBCountState (A : Set) : Set where
  constructor lcbCountState
  field valuesCount : CountFunction {A}
        totalCount : ℕ
open LCBCountState public

record LCBCountKernel : Set₁ where
  constructor lcbCountKernel
  field bonus : ℕ → IntCode
open LCBCountKernel public

finiteLCBBonus8 : ℕ → IntCode
finiteLCBBonus8 zero = intCodeOfNat 127
finiteLCBBonus8 (succ zero) = intCodeOfNat 63
finiteLCBBonus8 (succ (succ zero)) = intCodeOfNat 31
finiteLCBBonus8 (succ (succ (succ zero))) = intCodeOfNat 15
finiteLCBBonus8 (succ (succ (succ (succ zero)))) = intCodeOfNat 7
finiteLCBBonus8 (succ (succ (succ (succ (succ zero))))) = intCodeOfNat 3
finiteLCBBonus8 (succ (succ (succ (succ (succ (succ zero)))))) = intCodeOfNat 1
finiteLCBBonus8 _ = zeroIntCode

lcbNegate : IntCode → IntCode
lcbNegate x = intCodeNeg x

scoreA : ∀ {A : Set} → QFunction {A} → CountFunction {A} → ℕ → IntCode
scoreA q c a = intCodeAdd (q a) (lcbNegate (finiteLCBBonus8 (c a)))

lcbScore : ∀ {A : Set} → LCBCountKernel → LCBCountState A → CriticState A → QFunction {A}
lcbScore L c q a = intCodeAdd (values q a) (lcbNegate (bonus L (valuesCount c a)))

sparsemaxTemperature : ℕ
sparsemaxTemperature = 16

ScoreEntry : Set
ScoreEntry = IntCode × ℕ

intCodeValueInjective : ∀ {x y : IntCode} → intCodeValue x ＝ intCodeValue y → x ＝ y
intCodeValueInjective refl = refl

scoreList : ∀ {A : Set} → ActionSpace A → QFunction {A} → CountFunction {A} → List ScoreEntry
scoreList {A} K q c = map (λ a → (scoreA {A = A} q c a , a)) (candidates K)

data ComparisonResult : Set where
  less equal greater : ComparisonResult

compareInt8 : IntCode → IntCode → ComparisonResult
compareInt8 x y with ℤ-trichotomous (intCodeValue x) (intCodeValue y)
... | inl _ = less
... | inr (inl _) = equal
... | inr (inr _) = greater

compareNat : ℕ → ℕ → ComparisonResult
compareNat zero zero = equal
compareNat zero (succ _) = less
compareNat (succ _) zero = greater
compareNat (succ m) (succ n) = compareNat m n

scoreBefore : ScoreEntry → ScoreEntry → Bool
scoreBefore (s₁ , a₁) (s₂ , a₂) with compareInt8 s₁ s₂
... | less = false
... | greater = true
... | equal with compareNat a₁ a₂
... | less = false
... | equal = true
... | greater = true

insertScore : ScoreEntry → List ScoreEntry → List ScoreEntry
insertScore x [] = x ∷ []
insertScore x (y ∷ ys) with scoreBefore x y
... | true = x ∷ y ∷ ys
... | false = y ∷ insertScore x ys

sortScores : List ScoreEntry → List ScoreEntry
sortScores [] = []
sortScores (x ∷ xs) = insertScore x (sortScores xs)

natAt : ℕ → List ℕ → ℕ
natAt k [] = zero
natAt zero (x ∷ xs) = x
natAt (succ k) (x ∷ xs) = natAt k xs

sumList : List ℕ → ℕ
sumList [] = zero
sumList (x ∷ xs) = x + sumList xs

------------------------------------------------------------------------
-- Integer LayerNorm kernel.
--
-- IntCode wraps an unbounded mathematical integer; it is not a machine byte.  The normalization arithmetic therefore
-- remains integral and the normalized output is represented as an exact
-- integer ratio.  A certificate supplies the non-zero square root of
-- the integer radicand; no floating-point approximation enters the
-- proof surface.
------------------------------------------------------------------------

integerCodeSum : List IntCode → Int
integerCodeSum [] = pos 0
integerCodeSum (x ∷ xs) = intCodeValue x +Int integerCodeSum xs

integerCodeSumList : List Int → Int
integerCodeSumList [] = pos 0
integerCodeSumList (x ∷ xs) = x +Int integerCodeSumList xs

integerLayerNormCenteredNumerator :
  List IntCode → IntCode → Int
integerLayerNormCenteredNumerator xs x =
  (pos (length xs)) *Int intCodeValue x +Int intNeg (integerCodeSum xs)

integerLayerNormCenteredNumerators :
  List IntCode → List Int
integerLayerNormCenteredNumerators xs =
  map
    (λ x → integerLayerNormCenteredNumerator xs x)
    xs

integerLayerNormSquare : Int → Int
integerLayerNormSquare z = z *Int z

integerLayerNormVarianceNumerator :
  List IntCode → Int
integerLayerNormVarianceNumerator xs =
  integerCodeSumList
    (map
      integerLayerNormSquare
      (integerLayerNormCenteredNumerators xs))

integerLayerNormEpsilonContribution :
  List IntCode → ℕ → Int
integerLayerNormEpsilonContribution xs epsilon =
  intCodeValue
    (intCodeMul
      (intCodeOfNat epsilon)
      (intCodeMul (intCodeOfNat (length xs)) (intCodeOfNat (length xs))))

integerLayerNormRadicand :
  List IntCode → ℕ → Int
integerLayerNormRadicand xs epsilon =
  integerLayerNormVarianceNumerator xs
  +Int
  integerLayerNormEpsilonContribution xs epsilon

record IntegerLayerNormConfig : Set where
  constructor integerLayerNormConfig
  field fixedScale gamma beta : IntCode
open IntegerLayerNormConfig public

record IntegerLayerNormCertificate
  (xs : List IntCode) : Set where
  constructor integerLayerNormCertificate
  field
    epsilon : ℕ
    root : ℕ
    rootSquared :
      intCodeValue
        (intCodeMul (intCodeOfNat root) (intCodeOfNat root)) ＝
      integerLayerNormRadicand xs epsilon
    rootNonZero : root ≠ zero
open IntegerLayerNormCertificate public

record IntegerLayerNormValue : Set where
  constructor mkIntegerLayerNormValue
  field
    numerator : Int
    denominator : ℕ
    denominatorNonZero : denominator ≠ zero
open IntegerLayerNormValue public

integerLayerNormValue :
  ∀ {xs : List IntCode} →
  IntegerLayerNormConfig →
  IntegerLayerNormCertificate xs →
  IntCode →
  IntegerLayerNormValue
integerLayerNormValue {xs} config certificate x =
  mkIntegerLayerNormValue
    (intCodeValue (gamma config) *Int
      (intCodeValue (fixedScale config) *Int
        integerLayerNormCenteredNumerator xs x)
     +Int
     (intCodeValue (beta config) *Int (pos (root certificate))))
    (root certificate)
    (rootNonZero certificate)


intCodeMagnitude : IntCode → ℕ
intCodeMagnitude (intCode (pos n)) = n
intCodeMagnitude (intCode (negsucc n)) = succ n

infixl 6 _∸_
_∸_ : ℕ → ℕ → ℕ
zero ∸ n = zero
succ m ∸ zero = succ m
succ m ∸ succ n = m ∸ n

topCodes : ℕ → List ScoreEntry → List ℕ
topCodes zero xs = []
topCodes (succ k) [] = []
topCodes (succ k) ((x , a) ∷ xs) = intCodeMagnitude x ∷ topCodes k xs

-- TypeTopology arithmetic aliases stay local: do not import the agda2hs
-- Prelude here, since its builtin Nat is a different source type.
infixl 7 _*ℕ_
_*ℕ_ : ℕ → ℕ → ℕ
x *ℕ zero = zero
x *ℕ succ y = x + x *ℕ y

infixl 6 _+ℕ_
_+ℕ_ : ℕ → ℕ → ℕ
_+ℕ_ = _+_

supportValid : List ScoreEntry → ℕ → ℕ → BoolLike
supportValid xs temperature k with natLt (sumList (topCodes k xs)) (((k *ℕ natAt (k ∸ 1) (topCodes k xs)) +ℕ temperature))
... | enabled = enabled
... | disabled = disabled

searchSupport : List ScoreEntry → ℕ → ℕ → ℕ → ℕ → ℕ
searchSupport xs temperature zero current best = best
searchSupport xs temperature (succ n) current best with supportValid xs temperature current
... | enabled = searchSupport xs temperature n (succ current) (maxNat best current)
... | disabled = searchSupport xs temperature n (succ current) best

supportSize : ∀ {A : Set} → ActionSpace A → QFunction {A} → CountFunction {A} → ℕ
supportSize K q c = searchSupport (sortScores (scoreList K q c)) sparsemaxTemperature (length (candidates K)) (succ zero) (succ zero)

record SparseWeight : Set where
  constructor sparseWeight
  field numerator denominator : ℕ
open SparseWeight public

sparsemaxWeight : ∀ {A : Set} → ActionSpace A → QFunction {A} → CountFunction {A} → ℕ → SparseWeight
sparsemaxWeight {A} K q c a = sparseWeight (((k *ℕ intCodeMagnitude (scoreA {A = A} q c a)) +ℕ sparsemaxTemperature) ∸ s) (k *ℕ sparsemaxTemperature)
  where
    xs = sortScores (scoreList K q c)
    k = supportSize K q c
    s = sumList (topCodes k xs)

weightPositive : SparseWeight → BoolLike
weightPositive (sparseWeight n d) with natEq n zero
... | enabled = disabled
... | disabled = enabled

selectPositive : ∀ {A : Set} → ActionSpace A → QFunction {A} → CountFunction {A} → List ScoreEntry → ℕ
selectPositive K q c [] = witness K
selectPositive K q c ((s , a) ∷ xs) with weightPositive (sparsemaxWeight K q c a)
... | enabled = a
... | disabled = selectPositive K q c xs

sparsemaxPolicy : ∀ {A : Set} → ActionSpace A → QFunction {A} → CountFunction {A} → ℕ
sparsemaxPolicy K q c = selectPositive K q c (sortScores (scoreList K q c))

------------------------------------------------------------------------
-- Exact sparsemax behavior-policy readout.
-- The weight map is kept separate from the selected-action policy.
-- No probability normalization is claimed by this definition.
------------------------------------------------------------------------

updateLCBCount : ∀ {A : Set} → ℕ → LCBCountState A → LCBCountState A
updateLCBCount {A} a (lcbCountState counts total) =
  lcbCountState (incAt {A = A} counts a) (succ total)

------------------------------------------------------------------------
-- TypeTopology Rationals supplies the canonical exact rational carrier.
-- The legacy Dyadic helper names remain stable for theorem/registry
-- surfaces, but their carrier is now TypeTopology's rational type.
------------------------------------------------------------------------

Dyadic : Set
Dyadic = ℚ

fromNatDyadic : ℕ → ℕ → Dyadic
fromNatDyadic n exponent =
  toℚ (pos n , exponent)

dyadicNumerator : Dyadic → ℕ
dyadicNumerator ((pos n , d) , _) = n
dyadicNumerator ((negsucc n , d) , _) = zero

dyadicDenominator : Dyadic → ℕ
dyadicDenominator ((z , d) , _) =
  succ d

dyadicDivide : ℕ → Dyadic → ℕ
dyadicDivide n ((z , d) , _) =
  pr₁ (division n d)

qLog8 : IntCode → Dyadic
qLog8 x with intCodeMagnitude x
... | zero = fromNatDyadic 1 zero
... | succ n = fromNatDyadic (128 ∸ succ n) (succ n)

munchausenScale8 : ℕ
munchausenScale8 = 16

signedDyadicBias8 : Dyadic → IntCode
signedDyadicBias8 q with dyadicNumerator q
... | zero = zeroIntCode
... | succ n = intCodeNeg
  (intCodeOfNat
    (dyadicDivide
      (munchausenScale8 *ℕ succ n)
      q))

qLog2Bias8 : IntCode → IntCode
qLog2Bias8 x =
  signedDyadicBias8 (qLog8 x)

negativeAlpha8 : IntCode
negativeAlpha8 = intCodeOfNat 255

record SignedQLogControl : Set where
  constructor signedQLogControl
  field mode coefficient : IntCode
open SignedQLogControl public

canonicalQLogControl : SignedQLogControl
canonicalQLogControl =
  signedQLogControl negativeAlpha8 negativeAlpha8

qLogSignal : SignedQLogControl → IntCode → IntCode
qLogSignal c x = intCodeAdd x (coefficient c)

data HardSign : Set where
  negativeSign zeroSign positiveSign : HardSign

hardSignNonnegative : IntCode → HardSign
hardSignNonnegative (intCode (pos 0)) = zeroSign
hardSignNonnegative (intCode (pos (succ n))) = positiveSign
hardSignNonnegative (intCode (negsucc n)) = negativeSign

hardSign : IntCode → HardSign
hardSign (intCode (pos 0)) = zeroSign
hardSign (intCode (pos (succ n))) = positiveSign
hardSign (intCode (negsucc n)) = negativeSign

hardSignGate : IntCode → IntCode
hardSignGate x with hardSign x
... | negativeSign = intCodeOfNat 255
... | zeroSign = zeroIntCode
... | positive = oneIntCode

two8 : IntCode
two8 = intCodeAdd oneIntCode oneIntCode

relu8 : IntCode → IntCode
relu8 x with hardSign x
... | negativeSign = zeroIntCode
... | zeroSign = zeroIntCode
... | positive = x

leaky2 : IntCode → IntCode
leaky2 x with hardSign x
... | negativeSign = intCodeMul two8 x
... | zeroSign = zeroIntCode
... | positive = x

------------------------------------------------------------------------
-- Monoid LSTM recurrent core.
--
-- One input acts as an affine endomorphism of cell state.  Affine
-- composition is the carrier monoid; recurrent prefixes therefore admit
-- exact scan composition.  Hidden state is derived from the new cell
-- state plus the signed input feature.  Persistent matrix/noise/control
-- channels remain explicit learner state, preserving the old theorem
-- surface needed by downstream modules without retaining GRU dynamics.
------------------------------------------------------------------------

record MonoidLSTMMatrices : Set where
  constructor monoidLSTMMatrices
  field matrixZ matrixR matrixH : IntCode
open MonoidLSTMMatrices public

record MonoidLSTMNoise : Set where
  constructor monoidLSTMNoise
  field noiseZ noiseR noiseH : IntCode
open MonoidLSTMNoise public

record MonoidLSTMControl : Set where
  constructor monoidLSTMControl
  field optimizerToken l2Token : IntCode
open MonoidLSTMControl public

record MonoidAffine : Set where
  constructor monoidAffine
  field slope offset : IntCode
open MonoidAffine public

_∘ₘ_ : MonoidAffine → MonoidAffine → MonoidAffine
(monoidAffine a₁ b₁) ∘ₘ (monoidAffine a₂ b₂) =
  monoidAffine
    (intCodeMul a₁ a₂)
    (intCodeAdd (intCodeMul a₁ b₂) b₁)

monoidAffine-id : MonoidAffine
monoidAffine-id = monoidAffine oneIntCode zeroIntCode

monoidAffine-assoc : ∀ a b c → (a ∘ₘ b) ∘ₘ c ＝ a ∘ₘ (b ∘ₘ c)
monoidAffine-assoc (monoidAffine a₁ b₁) (monoidAffine a₂ b₂) (monoidAffine a₃ b₃) =
  cong₂ monoidAffine
    (intCode*-assoc a₁ a₂ a₃)
    (trans
      (cong₂ intCodeAdd
        (intCode*-assoc a₁ a₂ b₃)
        refl)
      (trans
        (sym (intCode+-assoc
          (intCodeMul a₁ (intCodeMul a₂ b₃))
          (intCodeMul a₁ b₂)
          b₁))
        (ap
          (λ z → intCodeAdd z b₁)
          (sym (intCode*-distribˡ
            a₁
            (intCodeMul a₂ b₃)
            b₂)))))

monoidAffine-idˡ : ∀ a → monoidAffine-id ∘ₘ a ＝ a
monoidAffine-idˡ (monoidAffine a b) =
  cong₂ monoidAffine
    (intCode*-idˡ a)
    (trans
      (ap (λ z → intCodeAdd z zeroIntCode) (intCode*-idˡ b))
      (intCode+-idʳ b))

monoidAffine-idʳ : ∀ a → a ∘ₘ monoidAffine-id ＝ a
monoidAffine-idʳ (monoidAffine a b) =
  cong₂ monoidAffine
    (intCode*-idʳ a)
    (trans
      (ap (λ z → intCodeAdd z b) (intCode*-zeroʳ a))
      (intCode+-idˡ b))

applyMonoidAffine : MonoidAffine → IntCode → IntCode
applyMonoidAffine (monoidAffine a b) c =
  intCodeAdd (intCodeMul a c) b

data MonoidLSTMGate : Set where
  monoidHold monoidWrite monoidReset monoidAccum : MonoidLSTMGate

monoidLSTMGateOf : IntCode → MonoidLSTMGate
monoidLSTMGateOf (intCode (pos 0)) = monoidHold
monoidLSTMGateOf (intCode (pos (succ n))) = monoidAccum
monoidLSTMGateOf (intCode (negsucc n)) = monoidReset

monoidLSTMCellStep : MonoidLSTMGate → IntCode → IntCode → IntCode
monoidLSTMCellStep monoidHold c x = c
monoidLSTMCellStep monoidWrite c x = leaky2 x
monoidLSTMCellStep monoidReset c x = zeroIntCode
monoidLSTMCellStep monoidAccum c x = intCodeAdd c (leaky2 x)

monoidLSTMAffineOf : MonoidLSTMGate → IntCode → MonoidAffine
monoidLSTMAffineOf monoidHold x = monoidAffine oneIntCode zeroIntCode
monoidLSTMAffineOf monoidWrite x = monoidAffine zeroIntCode (leaky2 x)
monoidLSTMAffineOf monoidReset x = monoidAffine zeroIntCode zeroIntCode
monoidLSTMAffineOf monoidAccum x = monoidAffine oneIntCode (leaky2 x)

monoidLSTMCellStep-is-affine :
  ∀ g c x →
  monoidLSTMCellStep g c x ＝
  applyMonoidAffine (monoidLSTMAffineOf g x) c
monoidLSTMCellStep-is-affine monoidHold c x =
  trans
    (sym (intCode*-idˡ c))
    (sym (intCode+-idʳ (intCodeMul oneIntCode c)))
monoidLSTMCellStep-is-affine monoidWrite c x =
  trans
    (sym (intCode+-idˡ (leaky2 x)))
    (ap
      (λ z → intCodeAdd z (leaky2 x))
      (sym (intCode*-zeroˡ c)))
monoidLSTMCellStep-is-affine monoidReset c x =
  trans
    (sym (intCode+-idˡ zeroIntCode))
    (ap
      (λ z → intCodeAdd z zeroIntCode)
      (sym (intCode*-zeroˡ c)))
monoidLSTMCellStep-is-affine monoidAccum c x =
  ap (λ z → intCodeAdd z (leaky2 x)) (sym (intCode*-idˡ c))

scanMonoidAffine : List IntCode → MonoidAffine
scanMonoidAffine [] = monoidAffine-id
scanMonoidAffine (x ∷ xs) =
  scanMonoidAffine xs ∘ₘ monoidLSTMAffineOf (monoidLSTMGateOf x) x

scanMonoidAffine-cons :
  ∀ x xs →
  scanMonoidAffine (x ∷ xs) ＝
  scanMonoidAffine xs ∘ₘ monoidLSTMAffineOf (monoidLSTMGateOf x) x
scanMonoidAffine-cons x xs = refl

runMonoidLSTMCell : List IntCode → IntCode → IntCode
runMonoidLSTMCell xs c₀ =
  applyMonoidAffine (scanMonoidAffine xs) c₀

record MonoidLSTMState : Set where
  constructor monoidLSTMState
  field
    hiddenState : IntCode
    cellState : IntCode
    matrixState : MonoidLSTMMatrices
    noiseState : MonoidLSTMNoise
    controlState : MonoidLSTMControl
open MonoidLSTMState public

identityMonoidLSTMMatrices : MonoidLSTMMatrices
identityMonoidLSTMMatrices = monoidLSTMMatrices oneIntCode oneIntCode oneIntCode

zeroMonoidLSTMNoise : MonoidLSTMNoise
zeroMonoidLSTMNoise = monoidLSTMNoise zeroIntCode zeroIntCode zeroIntCode

zeroMonoidLSTMControl : MonoidLSTMControl
zeroMonoidLSTMControl = monoidLSTMControl zeroIntCode zeroIntCode

monoidLSTMHiddenStep : IntCode → IntCode → IntCode → IntCode
monoidLSTMHiddenStep h c x =
  intCodeAdd c (leaky2 (intCodeAdd h x))

monoidLSTMStep : MonoidLSTMState → IntCode → MonoidLSTMState
monoidLSTMStep
  (monoidLSTMState h c m n g)
  x =
  let c₁ = monoidLSTMCellStep (monoidLSTMGateOf x) c x
      h₁ = monoidLSTMHiddenStep h c₁ x
  in monoidLSTMState h₁ c₁ m n g

persistentMonoidLSTM :
  MonoidLSTMState →
  MonoidLSTMMatrices × (MonoidLSTMNoise × MonoidLSTMControl)
persistentMonoidLSTM (monoidLSTMState h c m n g) = m , (n , g)

persistentMonoidLSTM-preservation :
  ∀ (s : MonoidLSTMState) (x : IntCode) →
  persistentMonoidLSTM (monoidLSTMStep s x) ＝
  persistentMonoidLSTM s
persistentMonoidLSTM-preservation
  (monoidLSTMState h c m n g) x = refl

monoidLSTMParameterPersistence :
  ∀ (s : MonoidLSTMState) (x : IntCode) →
  (matrixState (monoidLSTMStep s x) ＝ matrixState s) ×
  ((noiseState (monoidLSTMStep s x) ＝ noiseState s) ×
   (controlState (monoidLSTMStep s x) ＝ controlState s))
monoidLSTMParameterPersistence
  (monoidLSTMState h c m n g) x =
  refl , (refl , refl)

MonoidLSTMEquivalent : MonoidLSTMState → MonoidLSTMState → Set
MonoidLSTMEquivalent s t =
  persistentMonoidLSTM s ＝ persistentMonoidLSTM t

monoidLSTMStep-respects-equivalence :
  ∀ (s t : MonoidLSTMState) (x : IntCode) →
  MonoidLSTMEquivalent s t →
  MonoidLSTMEquivalent (monoidLSTMStep s x) (monoidLSTMStep t x)
monoidLSTMStep-respects-equivalence s t x eq =
  trans
    (persistentMonoidLSTM-preservation s x)
    (trans eq (sym (persistentMonoidLSTM-preservation t x)))

------------------------------------------------------------------------
-- Compatibility surface for downstream theorem modules.
-- GRU names are legacy aliases; canonical semantics are MonoidLSTM.
------------------------------------------------------------------------

GRUMatrices : Set
GRUMatrices = MonoidLSTMMatrices

GRUNoise : Set
GRUNoise = MonoidLSTMNoise

GlobalControl : Set
GlobalControl = MonoidLSTMControl

GRUState : Set
GRUState = MonoidLSTMState

gruMatrices : IntCode → IntCode → IntCode → GRUMatrices
gruMatrices a b c = monoidLSTMMatrices a b c

gruNoise : IntCode → IntCode → IntCode → GRUNoise
gruNoise a b c = monoidLSTMNoise a b c

mkGlobalControl : IntCode → IntCode → GlobalControl
mkGlobalControl a b = monoidLSTMControl a b

gruState :
  IntCode →
  IntCode →
  MonoidLSTMMatrices →
  MonoidLSTMNoise →
  MonoidLSTMControl →
  MonoidLSTMState
gruState = monoidLSTMState

identityGRUMatrices : GRUMatrices
identityGRUMatrices = identityMonoidLSTMMatrices

zeroGRUNoise : GRUNoise
zeroGRUNoise = zeroMonoidLSTMNoise

zeroGlobalControl : GlobalControl
zeroGlobalControl = zeroMonoidLSTMControl

dyadicCode : Dyadic → IntCode
dyadicCode q = intCodeOfNat (dyadicNumerator q)

identityActivation8 : IntCode → IntCode
identityActivation8 x = x

identityActivation8-law : ∀ x → identityActivation8 x ＝ x
identityActivation8-law x = refl

identityActivation8-zero : identityActivation8 zeroIntCode ＝ zeroIntCode
identityActivation8-zero = refl

gruCandidate8 : IntCode → IntCode → IntCode
gruCandidate8 h x = intCodeAdd h x

complement128 : IntCode → IntCode
complement128 g = intCodeSub oneIntCode g

mix8 : IntCode → IntCode → IntCode → IntCode
mix8 g old new =
  intCodeAdd
    (intCodeMul (complement128 g) old)
    (intCodeMul g new)

gateCode : Signed → IntCode
gateCode (signedNeg n) = zeroIntCode
gateCode signedZer = zeroIntCode
gateCode (signedPos n) = oneIntCode

gateFromInput : IntCode → IntCode
gateFromInput x = gateCode (signedCode x)

monoidLSTMRecurrentStep : MonoidLSTMState → IntCode → MonoidLSTMState
monoidLSTMRecurrentStep = monoidLSTMStep

gruStep : GRUState → IntCode → GRUState
gruStep = monoidLSTMStep

persistentGRU :
  GRUState →
  GRUMatrices × (GRUNoise × GlobalControl)
persistentGRU = persistentMonoidLSTM

persistent-preservation :
  ∀ (s : GRUState) (x : IntCode) →
  persistentGRU (gruStep s x) ＝ persistentGRU s
persistent-preservation s x =
  persistentMonoidLSTM-preservation s x

gruParameterPersistence :
  ∀ (s : GRUState) (x : IntCode) →
  (matrixState (gruStep s x) ＝ matrixState s) ×
  ((noiseState (gruStep s x) ＝ noiseState s) ×
   (controlState (gruStep s x) ＝ controlState s))
gruParameterPersistence s x =
  monoidLSTMParameterPersistence s x

GRUEquivalent : GRUState → GRUState → Set
GRUEquivalent = MonoidLSTMEquivalent

gruEquivalent-refl : ∀ s → GRUEquivalent s s
gruEquivalent-refl = monoidLSTMEquivalent-refl
  where
    monoidLSTMEquivalent-refl : ∀ s → MonoidLSTMEquivalent s s
    monoidLSTMEquivalent-refl s = refl

gruStep-respects-equivalence :
  ∀ (s t : GRUState) (x : IntCode) →
  GRUEquivalent s t →
  GRUEquivalent (gruStep s x) (gruStep t x)
gruStep-respects-equivalence =
  monoidLSTMStep-respects-equivalence

record GRUAction : Set₁ where
  constructor gruAction
  field runGRU : GRUState → GRUState
open GRUAction public

identityGRUAction : GRUAction
identityGRUAction = gruAction (λ s → s)

composeGRUAction : GRUAction → GRUAction → GRUAction
composeGRUAction f g =
  gruAction (λ s → runGRU f (runGRU g s))

gruActionAssociativity : ∀ f g h s →
  runGRU
    (composeGRUAction (composeGRUAction f g) h) s ＝
  runGRU
    (composeGRUAction f (composeGRUAction g h)) s
gruActionAssociativity f g h s = refl

inputGRUAction : IntCode → GRUAction
inputGRUAction x = gruAction (λ s → monoidLSTMStep s x)

record RecurrentNetwork (State Input : Set) : Set₁ where
  constructor recurrentNetwork
  field
    runNetwork : State → Input → State
open RecurrentNetwork public

canonicalMonoidLSTMRecurrentNetwork :
  RecurrentNetwork MonoidLSTMState IntCode
canonicalMonoidLSTMRecurrentNetwork =
  recurrentNetwork monoidLSTMStep

canonicalMonoidLSTMNetwork-law :
  ∀ (s : MonoidLSTMState) (x : IntCode) →
  runNetwork canonicalMonoidLSTMRecurrentNetwork s x ＝
  monoidLSTMStep s x
canonicalMonoidLSTMNetwork-law s x = refl

canonicalGRURecurrentNetwork : RecurrentNetwork GRUState IntCode
canonicalGRURecurrentNetwork =
  recurrentNetwork gruStep

canonicalGRUNetwork-law :
  ∀ (s : GRUState) (x : IntCode) →
  runNetwork canonicalGRURecurrentNetwork s x ＝
  monoidLSTMStep s x
canonicalGRUNetwork-law s x = refl

record Endomorphism (State : Set) : Set₁ where
  constructor endomorphism
  field
    applyEndomorphism : State → State
open Endomorphism public

identityEndomorphism : ∀ {State : Set} → Endomorphism State
identityEndomorphism = endomorphism (λ s → s)

composeEndomorphism :
  ∀ {State : Set} →
  Endomorphism State →
  Endomorphism State →
  Endomorphism State
composeEndomorphism f g =
  endomorphism
    (λ s →
      applyEndomorphism f
        (applyEndomorphism g s))

endomorphismAssociative :
  ∀ {State : Set} (f g h : Endomorphism State) s →
  applyEndomorphism
    (composeEndomorphism
      (composeEndomorphism f g)
      h)
    s
  ＝
  applyEndomorphism
    (composeEndomorphism
      f
      (composeEndomorphism g h))
    s
endomorphismAssociative f g h s = refl

recurrentInputEndomorphism :
  ∀ {State Input : Set} →
  RecurrentNetwork State Input →
  Input →
  Endomorphism State
recurrentInputEndomorphism R x =
  endomorphism (λ s → runNetwork R s x)

recurrentPrefixState :
  ∀ {State Input : Set} →
  RecurrentNetwork State Input →
  (ℕ → Input) →
  ℕ →
  State →
  State
recurrentPrefixState R xs zero s = s
recurrentPrefixState R xs (succ n) s =
  runNetwork R
    (recurrentPrefixState R xs n s)
    (xs n)

recurrentPrefixEndomorphism :
  ∀ {State Input : Set} →
  RecurrentNetwork State Input →
  (ℕ → Input) →
  ℕ →
  Endomorphism State
recurrentPrefixEndomorphism R xs zero =
  identityEndomorphism
recurrentPrefixEndomorphism R xs (succ n) =
  composeEndomorphism
    (recurrentInputEndomorphism R (xs n))
    (recurrentPrefixEndomorphism R xs n)

recurrentPrefix-correct :
  ∀ {State Input : Set}
  (R : RecurrentNetwork State Input)
  (xs : ℕ → Input)
  (n : ℕ)
  (s : State) →
  applyEndomorphism
    (recurrentPrefixEndomorphism R xs n)
    s
  ＝
  recurrentPrefixState R xs n s
recurrentPrefix-correct R xs zero s = refl
recurrentPrefix-correct R xs (succ n) s =
  ap
    (λ z → runNetwork R z (xs n))
    (recurrentPrefix-correct R xs n s)

shiftInput :
  ∀ {Input : Set} →
  (ℕ → Input) →
  ℕ →
  ℕ →
  Input
shiftInput xs m n = xs (m + n)

recurrentPrefix-split :
  ∀ {State Input : Set}
  (R : RecurrentNetwork State Input)
  (xs : ℕ → Input)
  (m n : ℕ)
  (s : State) →
  recurrentPrefixState R xs (m + n) s
  ＝
  recurrentPrefixState
    R
    (shiftInput xs m)
    n
    (recurrentPrefixState R xs m s)
recurrentPrefix-split R xs m zero s =
  ap
    (λ k → recurrentPrefixState R xs k s)
    (plus-zero m)
recurrentPrefix-split R xs m (succ n) s =
  trans
    (ap
      (λ k → recurrentPrefixState R xs k s)
      (plus-succ m n))
    (ap
      (λ z → runNetwork R z (xs (m + n)))
      (recurrentPrefix-split R xs m n s))

canonicalMonoidLSTM-recurrent-prefix-correct :
  ∀ (xs : ℕ → IntCode) (n : ℕ) (s : MonoidLSTMState) →
  applyEndomorphism
    (recurrentPrefixEndomorphism
      canonicalMonoidLSTMRecurrentNetwork
      xs
      n)
    s
  ＝
  recurrentPrefixState
    canonicalMonoidLSTMRecurrentNetwork
    xs
    n
    s
canonicalMonoidLSTM-recurrent-prefix-correct =
  recurrentPrefix-correct canonicalMonoidLSTMRecurrentNetwork

canonicalMonoidLSTM-recurrent-prefix-split :
  ∀ (xs : ℕ → IntCode) (m n : ℕ) (s : MonoidLSTMState) →
  recurrentPrefixState
    canonicalMonoidLSTMRecurrentNetwork
    xs
    (m + n)
    s
  ＝
  recurrentPrefixState
    canonicalMonoidLSTMRecurrentNetwork
    (shiftInput xs m)
    n
    (recurrentPrefixState
      canonicalMonoidLSTMRecurrentNetwork
      xs
      m
      s)
canonicalMonoidLSTM-recurrent-prefix-split =
  recurrentPrefix-split canonicalMonoidLSTMRecurrentNetwork

canonicalGRU-recurrent-prefix-correct :
  ∀ (xs : ℕ → IntCode) (n : ℕ) (s : GRUState) →
  applyEndomorphism
    (recurrentPrefixEndomorphism
      canonicalGRURecurrentNetwork
      xs
      n)
    s
  ＝
  recurrentPrefixState
    canonicalGRURecurrentNetwork
    xs
    n
    s
canonicalGRU-recurrent-prefix-correct =
  recurrentPrefix-correct canonicalGRURecurrentNetwork

canonicalGRU-recurrent-prefix-split :
  ∀ (xs : ℕ → IntCode) (m n : ℕ) (s : GRUState) →
  recurrentPrefixState
    canonicalGRURecurrentNetwork
    xs
    (m + n)
    s
  ＝
  recurrentPrefixState
    canonicalGRURecurrentNetwork
    (shiftInput xs m)
    n
    (recurrentPrefixState
      canonicalGRURecurrentNetwork
      xs
      m
      s)
canonicalGRU-recurrent-prefix-split =
  recurrentPrefix-split canonicalGRURecurrentNetwork

gruInputActionAssociativity :
  ∀ x y z s →
  runGRU
    (composeGRUAction
      (composeGRUAction
        (inputGRUAction x)
        (inputGRUAction y))
      (inputGRUAction z))
    s
  ＝
  runGRU
    (composeGRUAction
      (inputGRUAction x)
      (composeGRUAction
        (inputGRUAction y)
        (inputGRUAction z)))
    s
gruInputActionAssociativity x y z s = refl


gruStateInt8CoordinateCount : ℕ
gruStateInt8CoordinateCount = 10

criticInt8CoordinateCount : ℕ
criticInt8CoordinateCount = 2

gruPersistentQuotientCoordinateCount : ℕ
gruPersistentQuotientCoordinateCount = 8

fullLearnerInt8CoordinateCount : ℕ
fullLearnerInt8CoordinateCount = 24

fullLearnerInt8CoordinateCount-law : fullLearnerInt8CoordinateCount ＝ 24
fullLearnerInt8CoordinateCount-law = refl

record F4IntUState : Set where
  constructor f4IntUState
  field thetaQ rTheta eQ rE rL : IntCode
open F4IntUState public

record F4IntUKernel : Set₁ where
  constructor f4IntUKernel
  field globalL2 : IntCode
open F4IntUKernel public

f4ThetaFull : F4IntUState → IntCode
f4ThetaFull s = thetaQ s

f4ThetaFull-law : ∀ s → f4ThetaFull s ＝ thetaQ s
f4ThetaFull-law s = refl

l2Correction : IntCode → IntCode
l2Correction x = lcbNegate x

f4ThetaStep : F4IntUKernel → F4IntUState → IntCode → F4IntUState
f4ThetaStep K s g =
  f4IntUState
    (intCodeAdd (intCodeAdd (thetaQ s) g) (l2Correction (globalL2 K)))
    zeroIntCode (eQ s) (rE s) (rL s)

f4ParameterInvariant : ∀ (K : F4IntUKernel) (s : F4IntUState) (g : IntCode) →
  thetaQ (f4ThetaStep K s g) ＝
  intCodeAdd (intCodeAdd (thetaQ s) g) (l2Correction (globalL2 K))
f4ParameterInvariant K s g = refl

HaarAccumulator : Set
HaarAccumulator = IntCode × IntCode


------------------------------------------------------------------------
-- Haar-featured linear transformer.
--
-- Haar mixing remains exact integer arithmetic, now used as a feature map
-- inside a parameterized linear-attention accumulator.  The accumulator
-- is additive and therefore itself forms a monoid; sequence processing is
-- a pure left-to-right scan over rank-one feature updates.
------------------------------------------------------------------------

CanonicalHaarPair : Set
CanonicalHaarPair = IntCode × IntCode

canonicalHaarMix : IntCode → IntCode → CanonicalHaarPair
canonicalHaarMix x y =
  intCodeAdd x y , intCodeSub x y

canonicalHaarMix-left : ∀ x y →
  pr₁ (canonicalHaarMix x y) ＝ intCodeAdd x y
canonicalHaarMix-left x y = refl

canonicalHaarMix-right : ∀ x y →
  pr₂ (canonicalHaarMix x y) ＝ intCodeSub x y
canonicalHaarMix-right x y = refl

canonicalHaarMix-linear-form :
  ∀ x y →
  canonicalHaarMix x y ＝
  (intCodeAdd x y , intCodeSub x y)
canonicalHaarMix-linear-form x y = refl

canonicalReLU8 : IntCode → IntCode
canonicalReLU8 x with hardSign x
... | negativeSign = zeroIntCode
... | zeroSign = zeroIntCode
... | positiveSign = x

canonicalCReLU8 : IntCode → CanonicalHaarPair
canonicalCReLU8 x =
  canonicalReLU8 x , canonicalReLU8 (intCodeNeg x)

------------------------------------------------------------------------
-- Rational CReLU': CReLU with the negative ReLU branch replaced by the
-- exact rational softsign branch, matching the SignReLU shape while
-- keeping the paired positive/negative CReLU representation.
------------------------------------------------------------------------

canonicalSignReLU' : ℚ → ℚ
canonicalSignReLU' (((negsucc n , a) , _)) =
  toℚ (negsucc n , a + succ n)
canonicalSignReLU' q = q

CanonicalCReLUPrimePair : Set
CanonicalCReLUPrimePair = ℚ × ℚ

canonicalCReLU' : ℚ → CanonicalCReLUPrimePair
canonicalCReLU' x =
  canonicalSignReLU' x , canonicalSignReLU' (- x)

canonicalHaarFeature : IntCode → CanonicalHaarPair
canonicalHaarFeature x =
  canonicalHaarMix
    (pr₁ (canonicalCReLU8 x))
    (pr₂ (canonicalCReLU8 x))

canonicalHaarFeature-left : ∀ x →
  pr₁ (canonicalHaarFeature x) ＝
  intCodeAdd
    (pr₁ (canonicalCReLU8 x))
    (pr₂ (canonicalCReLU8 x))
canonicalHaarFeature-left x = refl

canonicalHaarFeature-right : ∀ x →
  pr₂ (canonicalHaarFeature x) ＝
  intCodeSub
    (pr₁ (canonicalCReLU8 x))
    (pr₂ (canonicalCReLU8 x))
canonicalHaarFeature-right x = refl

canonicalHaarOrthogonalCross :
  intCodeAdd
    (intCodeMul oneIntCode oneIntCode)
    (intCodeMul oneIntCode (intCodeNeg oneIntCode))
  ＝ zeroIntCode
canonicalHaarOrthogonalCross = refl

canonicalHaarFeatureReconstruct :
  ∀ x →
  let p = pr₁ (canonicalCReLU8 x)
      n = pr₂ (canonicalCReLU8 x)
  in intCodeSub p n ＝ x
canonicalHaarFeatureReconstruct
  (intCode (pos 0)) = refl
canonicalHaarFeatureReconstruct
  (intCode (pos (succ n))) = refl
canonicalHaarFeatureReconstruct
  (intCode (negsucc n)) = intCode+-idˡ (intCode (negsucc n))

canonicalHaarFeatureInjective :
  ∀ {x y} →
  canonicalCReLU8 x ＝ canonicalCReLU8 y →
  x ＝ y
canonicalHaarFeatureInjective {x} {y} eq =
  trans
    (sym (canonicalHaarFeatureReconstruct x))
    (trans
      (cong₂
        (λ a b → intCodeSub a b)
        (ap pr₁ eq)
        (ap pr₂ eq))
      (canonicalHaarFeatureReconstruct y))

record HaarFeaturedLinearTransformer : Set where
  constructor haarFeaturedLinearTransformer
  field
    qProjection kProjection vProjection : IntCode → IntCode
open HaarFeaturedLinearTransformer public

haarAccumulator-id : HaarAccumulator
haarAccumulator-id = zeroIntCode , zeroIntCode

haarAccumulator-op :
  HaarAccumulator → HaarAccumulator → HaarAccumulator
haarAccumulator-op (a₁ , b₁) (a₂ , b₂) =
  intCodeAdd a₁ a₂ , intCodeAdd b₁ b₂

haarAccumulator-op-assoc :
  ∀ x y z →
  haarAccumulator-op
    (haarAccumulator-op x y)
    z
  ＝
  haarAccumulator-op
    x
    (haarAccumulator-op y z)
haarAccumulator-op-assoc
  (a₁ , b₁)
  (a₂ , b₂)
  (a₃ , b₃) =
  cong₂ _,_
    (intCode+-assoc a₁ a₂ a₃)
    (intCode+-assoc b₁ b₂ b₃)

haarAccumulator-op-idˡ :
  ∀ x →
  haarAccumulator-op haarAccumulator-id x ＝ x
haarAccumulator-op-idˡ (a , b) =
  cong₂ _,_
    (intCode+-idˡ a)
    (intCode+-idˡ b)

haarAccumulator-op-idʳ :
  ∀ x →
  haarAccumulator-op x haarAccumulator-id ＝ x
haarAccumulator-op-idʳ (a , b) =
  cong₂ _,_
    (intCode+-idʳ a)
    (intCode+-idʳ b)

haarKeyValueContribution :
  HaarFeaturedLinearTransformer →
  IntCode →
  HaarAccumulator
haarKeyValueContribution T x =
  let (kp , kn) =
        canonicalHaarFeature
          (kProjection T x)
      v = vProjection T x
  in intCodeMul kp v , intCodeMul kn v

haarAccumulatorStep :
  HaarFeaturedLinearTransformer →
  HaarAccumulator →
  IntCode →
  HaarAccumulator
haarAccumulatorStep T s x =
  haarAccumulator-op s
    (haarKeyValueContribution T x)

haarQueryRead :
  HaarFeaturedLinearTransformer →
  HaarAccumulator →
  IntCode →
  IntCode
haarQueryRead T (sp , sn) x =
  let (qp , qn) =
        canonicalHaarFeature
          (qProjection T x)
  in intCodeAdd
       (intCodeMul qp sp)
       (intCodeMul qn sn)

haarLinearTransform :
  HaarFeaturedLinearTransformer →
  HaarAccumulator →
  List IntCode →
  List IntCode
haarLinearTransform T s₀ [] = []
haarLinearTransform T s₀ (x ∷ xs) =
  let s₁ = haarAccumulatorStep T s₀ x
  in haarQueryRead T s₁ x ∷
     haarLinearTransform T s₁ xs

haarLinearTransform-step-law :
  ∀ T s x →
  haarAccumulatorStep T s x ＝
  haarAccumulator-op s
    (haarKeyValueContribution T x)
haarLinearTransform-step-law T s x = refl

haarLinearTransform-associative-prefix :
  ∀ T s x y →
  haarAccumulatorStep T
    (haarAccumulatorStep T s x)
    y
  ＝
  haarAccumulator-op
    (haarAccumulatorStep T s x)
    (haarKeyValueContribution T y)
haarLinearTransform-associative-prefix T s x y = refl

canonicalHaarFeaturedTransformer :
  HaarFeaturedLinearTransformer
canonicalHaarFeaturedTransformer =
  haarFeaturedLinearTransformer
    identityActivation8
    identityActivation8
    identityActivation8

canonicalHaarFeaturedLinearScan :
  HaarAccumulator →
  List IntCode →
  List IntCode
canonicalHaarFeaturedLinearScan =
  haarLinearTransform canonicalHaarFeaturedTransformer


record FullLearnerState (A : Set) : Set₁ where
  constructor fullLearnerState
  field
    watkins : WatkinsState A
    gru : GRUState
    optimizer : F4IntUState
    lcbCounts : LCBCountState A
    qLogControl : SignedQLogControl
    qLogValue : Dyadic
    haarAccumulator : HaarAccumulator
open FullLearnerState public

record FullLearnerKernel (A : Set) : Set₁ where
  constructor mkFullLearnerKernel
  field
    actionSpaceK : ActionSpace A
    watkinsKernel : WatkinsKernel A
    optimizerKernel : F4IntUKernel
    lcbKernel : LCBCountKernel
open FullLearnerKernel public

CanonicalFullLearnerState : Set₁
CanonicalFullLearnerState = FullLearnerState 𝟙

CanonicalFullLearnerKernel : Set₁
CanonicalFullLearnerKernel = FullLearnerKernel 𝟙

canonicalPolicy : ∀ {A : Set} → FullLearnerKernel A → FullLearnerState A → ℕ
canonicalPolicy K s = sparsemaxPolicy (actionSpaceK K) (lcbScore (lcbKernel K) (lcbCounts s) (critic (watkins s))) (valuesCount (lcbCounts s))

canonicalPolicyWeight : ∀ {A : Set} → FullLearnerKernel A → FullLearnerState A → SparseWeight
canonicalPolicyWeight K s = sparsemaxWeight (actionSpaceK K) (lcbScore (lcbKernel K) (lcbCounts s) (critic (watkins s))) (valuesCount (lcbCounts s)) (canonicalPolicy K s)

canonicalPolicyWeightCode : ∀ {A : Set} → FullLearnerKernel A → FullLearnerState A → IntCode

BehaviorPolicy : Set
BehaviorPolicy = ℕ → SparseWeight

canonicalBehaviorPolicy :
  ∀ {A : Set} →
  FullLearnerKernel A →
  FullLearnerState A →
  BehaviorPolicy
canonicalBehaviorPolicy K s a =
  sparsemaxWeight
    (actionSpaceK K)
    (lcbScore
      (lcbKernel K)
      (lcbCounts s)
      (critic (watkins s)))
    (valuesCount (lcbCounts s))
    a

canonicalBehaviorAction :
  ∀ {A : Set} →
  FullLearnerKernel A →
  FullLearnerState A →
  ℕ
canonicalBehaviorAction K s = canonicalPolicy K s

canonicalBehaviorAction-law :
  ∀ {A : Set}
  (K : FullLearnerKernel A)
  (s : FullLearnerState A) →
  canonicalBehaviorAction K s ＝ canonicalPolicy K s
canonicalBehaviorAction-law K s = refl

canonicalPolicyWeightCode K s = intCodeOfNat (numerator (canonicalPolicyWeight K s))

HardSparse : ∀ {A : Set} → FullLearnerKernel A → FullLearnerState A → Set
HardSparse {A} K s =
  ∀ {a : ℕ} →
  a ≠ canonicalPolicy K s →
  numerator (sparsemaxWeight (actionSpaceK K) (lcbScore (lcbKernel K) (lcbCounts s) (critic (watkins s))) (valuesCount (lcbCounts s)) a) ＝ zero

SoftSparseBounded : ∀ {A : Set} →
  FullLearnerKernel A →
  FullLearnerState A →
  ℕ →
  Set
SoftSparseBounded {A} K s epsilon =
  ∀ {a : ℕ} →
  a ≠ canonicalPolicy K s →
  numerator
    (sparsemaxWeight
      (actionSpaceK K)
      (lcbScore (lcbKernel K) (lcbCounts s) (critic (watkins s)))
      (valuesCount (lcbCounts s))
      a)
  ≤ epsilon

hardSparse-to-softSparse-zero :
  ∀ {A}
  (K : FullLearnerKernel A)
  (s : FullLearnerState A) →
  HardSparse K s →
  SoftSparseBounded K s zero
hardSparse-to-softSparse-zero K s h {a} distinct =
  transport (λ n → n ≤ zero)
    (sym (h distinct))
    (zero-least zero)

softSparse-zero-to-hardSparse :
  ∀ {A}
  (K : FullLearnerKernel A)
  (s : FullLearnerState A) →
  SoftSparseBounded K s zero →
  HardSparse K s
softSparse-zero-to-hardSparse K s h {a} distinct =
  zero-least'' _ (h distinct)

replaceOptimizer : ∀ {A} → FullLearnerState A → F4IntUState → FullLearnerState A
replaceOptimizer s o = fullLearnerState (watkins s) (gru s) o
  (lcbCounts s) (qLogControl s) (qLogValue s) (haarAccumulator s)

canonicalPolicy-optimizer-invariant :
  ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) (o : F4IntUState) →
  canonicalPolicy K (replaceOptimizer s o) ＝ canonicalPolicy K s
canonicalPolicy-optimizer-invariant K s o = refl

maxCriticValueList : List IntCode → IntCode
maxCriticValueList [] = zeroIntCode
maxCriticValueList (x ∷ xs) with compareInt8 x (maxCriticValueList xs)
... | less = maxCriticValueList xs
... | equal = maxCriticValueList xs
... | greater = x

maxCriticValue8 : ∀ {A : Set} → ActionSpace A → CriticState A → IntCode
maxCriticValue8 K q = maxCriticValueList (map (λ a → values q a) (candidates K))

canonicalQLogBias : ∀ {A} → FullLearnerKernel A → FullLearnerState A → IntCode
canonicalQLogBias K s = qLog2Bias8 (canonicalPolicyWeightCode K s)

canonicalReward8 : ∀ {A} → FullLearnerKernel A → FullLearnerState A → IntCode
canonicalReward8 K s = canonicalPolicyWeightCode K s

canonicalDiscount8 : IntCode
canonicalDiscount8 = oneIntCode

canonicalGRUFeedback : ∀ {A} → FullLearnerState A → IntCode
canonicalGRUFeedback s = hiddenState (gru s)

canonicalF4L2Feedback : ∀ {A} → FullLearnerKernel A → FullLearnerState A → IntCode
canonicalF4L2Feedback K s =
  intCodeAdd
    (f4ThetaFull (optimizer s))
    (l2Correction (globalL2 (optimizerKernel K)))

canonicalQLogControlFeedback : ∀ {A} → FullLearnerState A → IntCode
canonicalQLogControlFeedback s = coefficient (qLogControl s)

canonicalQLogValueFeedback : ∀ {A} → FullLearnerState A → IntCode
canonicalQLogValueFeedback s = dyadicCode (qLogValue s)

canonicalEndogenousFeedback : ∀ {A} → FullLearnerKernel A → FullLearnerState A → IntCode
canonicalEndogenousFeedback K s =
  intCodeAdd
    (canonicalGRUFeedback s)
    (intCodeAdd
        (canonicalF4L2Feedback K s)
        (intCodeAdd
          (canonicalQLogControlFeedback s)
          (canonicalQLogValueFeedback s)))

canonicalWatkinsTarget : ∀ {A} → FullLearnerKernel A → FullLearnerState A → IntCode
canonicalWatkinsTarget K s =
  intCodeAdd
    (intCodeAdd
      (intCodeAdd (canonicalReward8 K s) (canonicalQLogBias K s))
      (intCodeMul canonicalDiscount8 (maxCriticValue8 (actionSpaceK K) (critic (watkins s)))))
    (canonicalEndogenousFeedback K s)

canonicalWatkinsTarget-law : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) →
  canonicalWatkinsTarget K s ＝
  intCodeAdd
    (intCodeAdd
      (intCodeAdd (canonicalReward8 K s) (canonicalQLogBias K s))
      (intCodeMul canonicalDiscount8 (maxCriticValue8 (actionSpaceK K) (critic (watkins s)))))
    (canonicalEndogenousFeedback K s)
canonicalWatkinsTarget-law K s = refl

canonicalQLogControlStep : ∀ {A} → FullLearnerKernel A → FullLearnerState A → SignedQLogControl
canonicalQLogControlStep K s =
  signedQLogControl negativeAlpha8 (canonicalQLogBias K s)

canonicalSignal : ∀ {A} → FullLearnerKernel A → FullLearnerState A → IntCode
canonicalSignal = canonicalWatkinsTarget

canonicalSignal-watkins-target : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) →
  canonicalSignal K s ＝ canonicalWatkinsTarget K s
canonicalSignal-watkins-target K s = refl

canonicalWatkinsStep : ∀ {A} → FullLearnerKernel A → FullLearnerState A → WatkinsState A
canonicalWatkinsStep K s =
  watkinsStep (watkinsKernel K)
  (watkinsState (critic (watkins s)) (canonicalSignal K s) (trace (watkins s)))

canonicalHaarAccumulatorStep :
  ∀ {A} →
  FullLearnerKernel A →
  FullLearnerState A →
  HaarAccumulator
canonicalHaarAccumulatorStep K s =
  haarAccumulatorStep
    canonicalHaarFeaturedTransformer
    (haarAccumulator s)
    (canonicalSignal K s)

canonicalHaarRecurrentInput :
  ∀ {A} →
  FullLearnerKernel A →
  FullLearnerState A →
  IntCode
canonicalHaarRecurrentInput K s =
  haarQueryRead
    canonicalHaarFeaturedTransformer
    (canonicalHaarAccumulatorStep K s)
    (canonicalSignal K s)

canonicalGRUStep : ∀ {A} → FullLearnerKernel A → FullLearnerState A → GRUState
canonicalGRUStep K s =
  gruStep
    (gru s)
    (canonicalHaarRecurrentInput K s)

canonicalPersistentGRUPreservation : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) →
  persistentGRU (canonicalGRUStep K s) ＝ persistentGRU (gru s)
canonicalPersistentGRUPreservation K s =
  persistent-preservation (gru s)
    (canonicalSignal K s)

canonicalRecurrentInput-law : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) →
  canonicalGRUStep K s ＝
  gruStep (gru s)
    (canonicalHaarRecurrentInput K s)
canonicalRecurrentInput-law K s = refl

canonicalOptimizerStep : ∀ {A} → FullLearnerKernel A → FullLearnerState A → F4IntUState
canonicalOptimizerStep K s = f4ThetaStep (optimizerKernel K) (optimizer s) (canonicalSignal K s)

canonicalOptimizerStep-qMunchausen-L2 : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) →
  canonicalOptimizerStep K s ＝
  f4ThetaStep
    (optimizerKernel K)
    (optimizer s)
    (canonicalWatkinsTarget K s)
canonicalOptimizerStep-qMunchausen-L2 K s = refl

canonicalCountStep : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) → LCBCountState A
canonicalCountStep K s = updateLCBCount (canonicalPolicy K s) (lcbCounts s)

canonicalQLogStep : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) → Dyadic
canonicalQLogStep K s = qLog8 (canonicalPolicyWeightCode K s)

canonicalFullStep : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) → FullLearnerState A
canonicalFullStep K s =
  fullLearnerState (canonicalWatkinsStep K s)
  (canonicalGRUStep K s)
  (canonicalOptimizerStep K s)
  (canonicalCountStep K s)
  (canonicalQLogControlStep K s)
  (canonicalQLogStep K s)
  (canonicalHaarAccumulatorStep K s)

canonicalFullStep-watkins : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) → watkins (canonicalFullStep K s) ＝ canonicalWatkinsStep K s
canonicalFullStep-watkins K s = refl

------------------------------------------------------------------------
-- Stream primitives for the canonical learner's observation API.
-- Agda2HS-supported coinduction uses Haskell.Prim.Thunk for lazy tails.
------------------------------------------------------------------------

module MonoidLSTMStreams where
  open import Haskell.Prelude
    using (Nat; zero; suc; List; []; _∷_; _≡_; refl; _+_)
  open import Agda.Primitive using (Level; _⊔_)
  open import Agda.Builtin.Size using (Size; Size<_; ∞)
  -- Agda2HS compiles recursive streams through this erased-size lazy tail.
  open import Haskell.Prim.Thunk using (Thunk; force)
  
  -- a stream carries the size of the observation depth available to its tail.
  -- Each tail is available at a strictly smaller size. This proves productivity
  -- through sized recursion rather than the guardedness checker.
  -- Agda2HS's supported coinduction encoding: a delayed, sized recursive tail.
  data Stream {ℓ : Level} (a : Set ℓ) (@0 i : Size) : Set ℓ where
    StreamCons : a → Thunk (Stream a) i → Stream a i
  
  streamHead : {ℓ : Level} {a : Set ℓ} {i : Size} → Stream a i → a
  streamHead (StreamCons value _) = value
  
  -- Inspect the constructor before introducing the smaller-size witness.
  -- The size inequality is non-fibrant under the two-level profile, so keep it
  -- out of the constructor-elimination context and force only afterward.
  streamDelayedTail :
    {ℓ : Level} {a : Set ℓ} {i : Size} →
    Stream a i → Thunk (Stream a) i
  streamDelayedTail (StreamCons _ delayed) = delayed

  {-# COMPILE AGDA2HS streamDelayedTail #-}

  streamTail :
    {ℓ : Level} {a : Set ℓ} {i : Size}
    (input : Stream a i) → {j : Size< i} → Stream a j
  streamTail input {j} = force (streamDelayedTail input) {j}
  
  {-# COMPILE AGDA2HS Stream #-}
  {-# COMPILE AGDA2HS streamHead #-}
  {-# COMPILE AGDA2HS streamTail #-}
  
  repeatStream :
    {ℓ : Level} {i : Size} {a : Set ℓ} → a → Stream a i
  repeatStream value =
    StreamCons value λ where
      .force → repeatStream value
  
  {-# COMPILE AGDA2HS repeatStream #-}
  
  mapStream :
    {ℓa ℓb : Level} {i : Size}
    {a : Set ℓa} {b : Set ℓb} →
    (a → b) → Stream a i → Stream b i
  mapStream f input =
    StreamCons (f (streamHead input)) λ where
      .force → mapStream f (streamTail input)
  
  {-# COMPILE AGDA2HS mapStream #-}
  
  -- Finite prefixes require an indefinitely observable stream. a merely-sized
  -- Stream i may only expose an unknown finite observation depth.
  streamPrefix : {ℓ : Level} {a : Set ℓ} → Nat → Stream a ∞ → List a
  streamPrefix 0 _ = []
  streamPrefix (suc n) input =
    streamHead input ∷ streamPrefix n (streamTail input)
  
  mapList : {ℓa ℓb : Level} {a : Set ℓa} {b : Set ℓb} → (a → b) → List a → List b
  mapList f [] = []
  mapList f (value ∷ values) = f value ∷ mapList f values
  
  cong :
    {ℓa ℓb : Level} {a : Set ℓa} {b : Set ℓb}
    (f : a → b) {left right : a} →
    left ≡ right → f left ≡ f right
  cong f refl = refl
  
  trans :
    {ℓ : Level} {a : Set ℓ} {left middle right : a} →
    left ≡ middle → middle ≡ right → left ≡ right
  trans refl second = second
  
  sym : {ℓ : Level} {a : Set ℓ} {left right : a} → left ≡ right → right ≡ left
  sym refl = refl
  
  mapListCong :
    {ℓa ℓb : Level} {a : Set ℓa} {b : Set ℓb}
    (f : a → b) {left right : List a} →
    left ≡ right → mapList f left ≡ mapList f right
  mapListCong f refl = refl
  
  mapStreamPrefix :
    {ℓa ℓb : Level} {a : Set ℓa} {b : Set ℓb}
    (n : Nat) (f : a → b) (input : Stream a ∞) →
    streamPrefix n (mapStream f input) ≡
    mapList f (streamPrefix n input)
  mapStreamPrefix 0 f input = refl
  mapStreamPrefix (suc n) f input =
    cong (λ rest → f (streamHead input) ∷ rest)
      (mapStreamPrefix n f (streamTail input))
  
  -- a stateful scan is the causal recurrence used by stream-processing
  -- programs. An LSTM transition can instantiate step once state/input types
  -- are fixed.
  scanStream :
    {ℓs ℓi : Level} {i : Size}
    {state : Set ℓs} {input : Set ℓi} →
    (state → input → state) →
    state → Stream input i → Stream state i
  scanStream step state inputs =
    StreamCons (step state (streamHead inputs)) λ where
      .force →
        scanStream
          step
          (step state (streamHead inputs))
          (streamTail inputs)
  
  {-# COMPILE AGDA2HS scanStream #-}
  
  -- The learner trace convention includes the initial state at observation zero.
  scanSeededStream :
    {ℓs ℓi : Level} {i : Size}
    {state : Set ℓs} {input : Set ℓi} →
    (state → input → state) →
    state → Stream input i → Stream state i
  scanSeededStream step state inputs =
    StreamCons state λ where
      .force →
        scanSeededStream
          step
          (step state (streamHead inputs))
          (streamTail inputs)
  
  {-# COMPILE AGDA2HS scanSeededStream #-}
  
  iterateStream :
    {ℓ : Level} {i : Size} {a : Set ℓ} →
    (a → a) → a → Stream a i
  iterateStream step state =
    StreamCons state λ where
      .force → iterateStream step (step state)
  
  {-# COMPILE AGDA2HS iterateStream #-}
  
  iterateList :
    {ℓ : Level} {a : Set ℓ} →
    Nat → (a → a) → a → List a
  -- Proof-side finite iterator used by iterateStreamPrefix. Keep it Agda-checked;
  -- Agda2HS's executable Nat pattern subset does not extract this recursion.
  iterateList 0 step state = []
  iterateList (suc n) step state =
    state ∷ iterateList n step (step state)
  
  scanList :
    {ℓs ℓi : Level} {state : Set ℓs} {input : Set ℓi} →
    (state → input → state) →
    state → List input → List state
  scanList step state [] = []
  scanList step state (input ∷ inputs) =
    step state input ∷ scanList step (step state input) inputs
  
  scanListCong :
    {ℓs ℓi : Level} {state : Set ℓs} {input : Set ℓi}
    (step : state → input → state)
    (state : state)
    {left right : List input} →
    left ≡ right →
    scanList step state left ≡ scanList step state right
  scanListCong step state refl = refl
  
  scanStreamPrefix :
    {ℓs ℓi : Level} {state : Set ℓs} {input : Set ℓi}
    (n : Nat)
    (step : state → input → state)
    (state : state)
    (inputs : Stream input ∞) →
    streamPrefix n (scanStream step state inputs) ≡
    scanList step state (streamPrefix n inputs)
  scanStreamPrefix 0 step state inputs = refl
  scanStreamPrefix (suc n) step state inputs =
    cong (λ rest → step state (streamHead inputs) ∷ rest)
      (scanStreamPrefix n step
        (step state (streamHead inputs))
        (streamTail inputs))
  
  -- Equal first-n input samples force equal first-n output samples. This is
  -- finite-observation causality, not decidable equality of infinite streams.
  iterateStreamPrefix :
    {ℓ : Level} {a : Set ℓ} →
    (n : Nat) (step : a → a) (initial : a) →
    streamPrefix n (iterateStream step initial) ≡
      iterateList n step initial
  iterateStreamPrefix zero step initial = refl
  iterateStreamPrefix (suc n) step initial =
    cong (λ rest → initial ∷ rest)
      (iterateStreamPrefix n step (step initial))
  
  CausalAt :
    {ℓi ℓo : Level} {input : Set ℓi} {output : Set ℓo} →
    Nat →
    (Stream input ∞ → Stream output ∞) →
    Set (ℓi ⊔ ℓo)
  CausalAt {input = input} n transformer =
    (left right : Stream input ∞) →
    streamPrefix n left ≡ streamPrefix n right →
    streamPrefix n (transformer left) ≡
    streamPrefix n (transformer right)
  
  mapStreamCausalAt :
    {ℓi ℓo : Level} {input : Set ℓi} {output : Set ℓo}
    (n : Nat) (f : input → output) →
    CausalAt n (mapStream f)
  mapStreamCausalAt n f left right samePrefix =
    trans
      (mapStreamPrefix n f left)
      (trans
        (mapListCong f samePrefix)
        (sym (mapStreamPrefix n f right)))
  
  scanStreamCausalAt :
    {ℓs ℓi : Level} {state : Set ℓs} {input : Set ℓi}
    (n : Nat)
    (step : state → input → state)
    (state : state) →
    CausalAt n (scanStream step state)
  scanStreamCausalAt n step state left right samePrefix =
    trans
      (scanStreamPrefix n step state left)
      (trans
        (scanListCong step state samePrefix)
        (sym (scanStreamPrefix n step state right)))
  
  -- Sized stream contexts represent successive suffixes whose available size
  -- decreases at each tail. a homogeneous same-size stream of streams would be
  -- incorrect: a suffix is available only at a smaller size.
  record StreamContext (i : Size) {ℓ : Level} (a : Set ℓ) : Set ℓ where
    coinductive
    field
      contextStream : Stream a i
      contextTail : ∀ {j : Size< i} → StreamContext j a
  
  open StreamContext public
  
  duplicate : {ℓ : Level} {i : Size} {a : Set ℓ} → Stream a i → StreamContext i a
  contextStream (duplicate input) = input
  contextTail (duplicate input) {j} =
    duplicate (streamTail input {j})
  
  extract : {ℓ : Level} {i : Size} {a : Set ℓ} → Stream a i → a
  extract = streamHead
  
  -- a co-Kleisli arrow is a context observation available at every size.
  -- extend applies that context to each successive suffix.
  extend :
    {ℓa ℓb : Level} {i : Size}
    {a : Set ℓa} {b : Set ℓb} →
    (∀ {j : Size} → Stream a j → b) →
    Stream a i → Stream b i
  extend context input =
    StreamCons (context (contextStream (duplicate input))) λ where
      .force →
        extend context (contextStream (contextTail (duplicate input)))
  
  
  record Bisim (i : Size) {ℓ : Level} {a : Set ℓ}
    (left right : Stream a i) : Set ℓ where
    coinductive
    field
      headsAgree : streamHead left ≡ streamHead right
      tailsBisimilar :
        ∀ {j : Size< i} →
        Bisim j (streamTail left {j}) (streamTail right {j})
  
  open Bisim public
  
  -- Map composition is proved coinductively by decreasing the observation size.
  mapStreamComposeBisim :
    {ℓ : Level} {i : Size} {a b c : Set ℓ}
    (f : b → c)
    (g : a → b)
    (input : Stream a i) →
    Bisim i
      (mapStream f (mapStream g input))
      (mapStream (λ value → f (g value)) input)
  mapStreamComposeBisim f g input .headsAgree = refl
  mapStreamComposeBisim f g input .tailsBisimilar {j} =
    mapStreamComposeBisim f g (streamTail input {j})
  
  -- Named fusion law: two successive maps agree with their composed map at
  -- every finite observation depth and, by Bisim, over the infinite stream.
  mapStreamFusionBisim :
    {ℓ : Level} {i : Size} {a b c : Set ℓ}
    (f : b → c)
    (g : a → b)
    (input : Stream a i) →
    Bisim i
      (mapStream f (mapStream g input))
      (mapStream (λ value → f (g value)) input)
  mapStreamFusionBisim = mapStreamComposeBisim
  
  mapListCompose :
    {ℓ : Level} {a b c : Set ℓ} (f : b → c) (g : a → b) (values : List a) →
    mapList f (mapList g values) ≡
    mapList (λ value → f (g value)) values
  mapListCompose f g [] = refl
  mapListCompose f g (value ∷ values) =
    cong (λ rest → f (g value) ∷ rest) (mapListCompose f g values)
  
  mapStreamFusionPrefix :
    {ℓ : Level} {a b c : Set ℓ}
    (n : Nat) (f : b → c) (g : a → b) (input : Stream a ∞) →
    streamPrefix n (mapStream f (mapStream g input)) ≡
    streamPrefix n (mapStream (λ value → f (g value)) input)
  mapStreamFusionPrefix n f g input =
    trans
      (mapStreamPrefix n f (mapStream g input))
      (trans
        (mapListCong f (mapStreamPrefix n g input))
        (trans
          (mapListCompose f g (streamPrefix n input))
          (sym (mapStreamPrefix n (λ value → f (g value)) input))))
  
  -- a state encoding fuses with a scan whenever it commutes with one transition.
  -- The proof is coinductive: each tail obligation reduces the commuting square,
  -- then recurses at the strictly smaller stream size.
  -- Equality composition and congruence are isolated from the sized
  -- coinductive field so that no equality is eliminated in a Size< context.
  streamCong :
    {ℓa ℓb : Level} {a : Set ℓa} {b : Set ℓb}
    (f : a → b) {x y : a} → x ≡ y → f x ≡ f y
  streamCong f refl = refl

  streamTrans :
    {ℓ : Level} {a : Set ℓ} {x y z : a} →
    x ≡ y → y ≡ z → x ≡ z
  streamTrans refl yz = yz

  scanMapFusionBisimAux :
    {ℓs ℓt ℓi : Level} {i : Size}
    {state : Set ℓs} {target : Set ℓt} {input : Set ℓi} →
    (encode : state → target) →
    (step : state → input → state) →
    (targetStep : target → input → target) →
    (stepFusion :
      (state : state) (input : input) →
      encode (step state input) ≡ targetStep (encode state) input) →
    (state : state) (targetState : target) →
    encode state ≡ targetState →
    (inputs : Stream input i) →
    Bisim i
      (mapStream encode (scanStream step state inputs))
      (scanStream targetStep targetState inputs)
  scanMapFusionBisimAux encode step targetStep stepFusion
    state targetState stateAgreement inputs .headsAgree =
      streamTrans
        (stepFusion state (streamHead inputs))
        (streamCong (λ value → targetStep value (streamHead inputs)) stateAgreement)
  scanMapFusionBisimAux encode step targetStep stepFusion
    state targetState stateAgreement inputs .tailsBisimilar {j} =
      scanMapFusionBisimAux
        encode
        step
        targetStep
        stepFusion
        (step state (streamHead inputs))
        (targetStep targetState (streamHead inputs))
        (streamTrans
          (stepFusion state (streamHead inputs))
          (streamCong (λ value → targetStep value (streamHead inputs)) stateAgreement))
        (streamTail inputs {j})

  scanMapFusionBisim :
    {ℓs ℓt ℓi : Level} {i : Size}
    {state : Set ℓs} {target : Set ℓt} {input : Set ℓi} →
    (encode : state → target) →
    (step : state → input → state) →
    (targetStep : target → input → target) →
    (stepFusion :
      (state : state) (input : input) →
      encode (step state input) ≡ targetStep (encode state) input) →
    (state : state) (inputs : Stream input i) →
    Bisim i
      (mapStream encode (scanStream step state inputs))
      (scanStream targetStep (encode state) inputs)
  scanMapFusionBisim encode step targetStep stepFusion state inputs =
    scanMapFusionBisimAux
      encode step targetStep stepFusion state (encode state) refl inputs
  
  -- Regression: successor encoding commutes with natural-number addition.
  -- Mapping successor over a running sum agrees with starting the scan
  -- from the successor state, at every finite observation and over the stream.
  scanSuccessorFusionStep :
    (state input : Nat) →
    suc (state + input) ≡ suc state + input
  scanSuccessorFusionStep state input = refl
  
  scanSuccessorFusionRegression :
    (state : Nat) (inputs : Stream Nat ∞) →
    Bisim ∞
      (mapStream suc (scanStream _+_ state inputs))
      (scanStream _+_ (suc state) inputs)
  scanSuccessorFusionRegression state inputs =
    scanMapFusionBisim
      suc
      _+_
      _+_
      scanSuccessorFusionStep
      state
      inputs
  
  bisimReflexive :
    {ℓ : Level} {i : Size} {a : Set ℓ} (input : Stream a i) → Bisim i input input
  bisimReflexive input .headsAgree = refl
  bisimReflexive input .tailsBisimilar {j} =
    bisimReflexive (streamTail input {j})
  
  extractDuplicateHead :
    {ℓ : Level} {a : Set ℓ} (input : Stream a ∞) →
    streamHead (contextStream (duplicate input)) ≡ streamHead input
  extractDuplicateHead input = refl
  
  -- extend extract is identity up to bisimulation, not a claim of decidable
  -- Leibniz equality for all infinite observations.
  extendExtractBisimilar :
    {ℓ : Level} {i : Size} {a : Set ℓ} (input : Stream a i) →
    Bisim i (extend extract input) input
  extendExtractBisimilar input .headsAgree = refl
  extendExtractBisimilar input .tailsBisimilar {j} =
    extendExtractBisimilar (streamTail input {j})
  
  ones : Stream Nat ∞
  ones = repeatStream (suc zero)
  
  onesPrefixRegression :
    streamPrefix (suc (suc (suc zero))) ones ≡
      suc zero ∷ suc zero ∷ suc zero ∷ []
  onesPrefixRegression = refl
  
  runningSum : Stream Nat ∞ → Stream Nat ∞
  runningSum = scanStream _+_ zero
  
  runningSumPrefixRegression :
    streamPrefix (suc (suc (suc zero))) (runningSum ones) ≡
      suc zero ∷ suc (suc zero) ∷ suc (suc (suc zero)) ∷ []
  runningSumPrefixRegression = refl

module MLS = MonoidLSTMStreams

------------------------------------------------------------------------
-- Productive observation of the canonical learner.
-- Stream structure is learner semantics; bisimulation laws live in the
-- theorem monolith. The size index bounds every tail observation.
------------------------------------------------------------------------

-- The embedded stream carrier and observation laws belong to this learner module.
-- The trace below iterates the actual canonical learner transition.
LearnerStream : (i : Size) → Set ℓ → Set ℓ
LearnerStream i A = MLS.Stream A i

learnerStreamHead :
  {i : Size} {A : Set ℓ} → LearnerStream i A → A
learnerStreamHead = MLS.streamHead

learnerStreamTail :
  {i : Size} {A : Set ℓ}
  (input : LearnerStream i A) →
  {j : Size< i} → LearnerStream j A
learnerStreamTail = MLS.streamTail

learnerStreamRepeat :
  {i : Size} {A : Set ℓ} → A → LearnerStream i A
learnerStreamRepeat = MLS.repeatStream

mapLearnerStream :
  {i : Size} {A B : Set ℓ} →
  (A → B) → LearnerStream i A → LearnerStream i B
mapLearnerStream = MLS.mapStream

canonicalLearnerTrace :
  {i : Size} {A : Set} →
  FullLearnerKernel A →
  FullLearnerState A →
  LearnerStream i (FullLearnerState A)
canonicalLearnerTrace {i} K initial =
  MLS.iterateStream {i = i} (canonicalFullStep K) initial

-- The finite observation law is stated over the stream implementation used
-- by the canonical learner, not over an independent stream definition.
canonicalLearnerTracePrefix :
  ∀ {A : Set}
    (K : FullLearnerKernel A)
    (initial : FullLearnerState A)
    (n : Nat) →
  MLS.streamPrefix n (canonicalLearnerTrace {i = ∞} K initial) ≡
    MLS.iterateList n (canonicalFullStep K) initial
canonicalLearnerTracePrefix K initial n =
  MLS.iterateStreamPrefix n (canonicalFullStep K) initial

learnerStreamAt :
  {i : Size} {A : Set ℓ} →
  ℕ →
  LearnerStream i A →
  A
learnerStreamAt zero trace = learnerStreamHead trace
learnerStreamAt (succ n) trace =
  learnerStreamAt n (learnerStreamTail trace)


iterateCanonical-step-shift :
  ∀ {A}
  (K : FullLearnerKernel A)
  (n : ℕ)
  (s : FullLearnerState A) →
  iterateCanonical K n (canonicalFullStep K s) ＝
  iterateCanonical K (succ n) s
iterateCanonical-step-shift K zero s = refl
iterateCanonical-step-shift K (succ n) s =
  ap (canonicalFullStep K) (iterateCanonical-step-shift K n s)

canonicalLearnerTraceAt :
  ∀ {A}
  (K : FullLearnerKernel A)
  (s : FullLearnerState A)
  (n : ℕ) →
  learnerStreamAt n (canonicalLearnerTrace K s) ＝
  iterateCanonical K n s
canonicalLearnerTraceAt K s zero = refl
canonicalLearnerTraceAt K s (succ n) =
  trans
    (canonicalLearnerTraceAt K (canonicalFullStep K s) n)
    (iterateCanonical-step-shift K n s)

-- Exact finite observation means every state predicate is invariant under
-- choosing the productive stream view versus the canonical iterator view.
-- Instantiating P with a state-indexed beta-optimality predicate transports
-- that property; it does not prove the predicate holds without reward facts.
canonicalLearnerTracePredicateAt :
  ∀ {A}
  (K : FullLearnerKernel A)
  (initial : FullLearnerState A)
  (n : ℕ)
  (P : FullLearnerState A → Set) →
  P (learnerStreamAt n (canonicalLearnerTrace K initial)) →
  P (iterateCanonical K n initial)
canonicalLearnerTracePredicateAt K initial n P property =
  transport P (canonicalLearnerTraceAt K initial n) property


canonicalFullStep-gru : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) → gru (canonicalFullStep K s) ＝ canonicalGRUStep K s
canonicalFullStep-gru K s = refl

canonicalFullStep-optimizer : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) → optimizer (canonicalFullStep K s) ＝ canonicalOptimizerStep K s
canonicalFullStep-optimizer K s = refl

canonicalFullStep-counts : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) → lcbCounts (canonicalFullStep K s) ＝ canonicalCountStep K s
canonicalFullStep-counts K s = refl

canonicalFullStep-qLog : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) → qLogValue (canonicalFullStep K s) ＝ canonicalQLogStep K s
canonicalFullStep-qLog K s = refl

canonicalFullStep-qLogControl : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) → qLogControl (canonicalFullStep K s) ＝ canonicalQLogControlStep K s
canonicalFullStep-qLogControl K s = refl

canonicalTotalCountStep : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) → totalCount (lcbCounts (canonicalFullStep K s)) ＝ succ (totalCount (lcbCounts s))
canonicalTotalCountStep K s = refl

canonicalNoFixedPoint :
  ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) →
  canonicalFullStep K s ≠ s
canonicalNoFixedPoint K s eq =
  plus-succ-not-self (totalCount (lcbCounts s)) zero
    (trans (plus-succ (totalCount (lcbCounts s)) zero)
      (trans (ap succ (plus-zero (totalCount (lcbCounts s))))
        (trans (sym (canonicalTotalCountStep K s))
          (ap (λ t → totalCount (lcbCounts t)) eq))))

iterateCanonical : ∀ {A} → FullLearnerKernel A → ℕ → FullLearnerState A → FullLearnerState A
iterateCanonical K zero s = s
iterateCanonical K (succ n) s = canonicalFullStep K (iterateCanonical K n s)

canonicalTotalCountAfter :
  ∀ {A} (K : FullLearnerKernel A) (n : ℕ) (s : FullLearnerState A) →
  totalCount (lcbCounts (iterateCanonical K n s)) ＝
  totalCount (lcbCounts s) + n
canonicalTotalCountAfter K zero s = sym (plus-zero (totalCount (lcbCounts s)))
canonicalTotalCountAfter K (succ n) s =
  trans
    (canonicalTotalCountStep K (iterateCanonical K n s))
    (trans
      (ap succ (canonicalTotalCountAfter K n s))
      (sym (plus-succ (totalCount (lcbCounts s)) n)))

canonicalAperiodic : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) (n : ℕ) → iterateCanonical K (succ n) s ≠ s
canonicalAperiodic K s n cyc = plus-succ-not-self (totalCount (lcbCounts s)) n
  (trans
    (sym (canonicalTotalCountAfter K (succ n) s))
    (ap (λ t → totalCount (lcbCounts t)) cyc))

canonicalOrbitNonFixed : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) (n : ℕ) → iterateCanonical K n s ≠ canonicalFullStep K (iterateCanonical K n s)
canonicalOrbitNonFixed K s n eq =
  canonicalNoFixedPoint K (iterateCanonical K n s) (eq ⁻¹)

canonicalNoNontrivialFiniteCycle : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) (n : ℕ) → iterateCanonical K (succ n) s ＝ s → 𝟘
canonicalNoNontrivialFiniteCycle K s n cyc = canonicalAperiodic K s n cyc

canonicalTotalCountIterate2 : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) → totalCount (lcbCounts (iterateCanonical K 2 s)) ＝ succ (succ (totalCount (lcbCounts s)))
canonicalTotalCountIterate2 K s = refl

canonicalNoCountedTwoCycle : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) → iterateCanonical K 2 s ＝ s → 𝟘
canonicalNoCountedTwoCycle K s cyc = succ-succ-not-self (totalCount (lcbCounts s))
  (trans (sym (canonicalTotalCountIterate2 K s))
    (ap (λ t → totalCount (lcbCounts t)) cyc))

temperatureCodeLaw : sparsemaxTemperature ＝ 16
temperatureCodeLaw = refl

pessimisticInit : IntCode
pessimisticInit = intCodeOfNat 128

pessimisticCritic : ∀ {A} → CriticState A
pessimisticCritic {A} = criticState (λ _ → pessimisticInit)

pessimisticCritic-law : ∀ {A} (i : ℕ) → values (pessimisticCritic {A = A}) i ＝ pessimisticInit
pessimisticCritic-law {A = A} i = refl

canonicalPersistent : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) → persistentGRU (canonicalGRUStep K s) ＝ persistentGRU (gru s)
canonicalPersistent = canonicalPersistentGRUPreservation

CanonicalToken : Set
CanonicalToken = Int

CanonicalTokenSequence : Set
CanonicalTokenSequence = List CanonicalToken

canonicalTokenEncode : CanonicalToken → IntCode
canonicalTokenEncode = intCode

-- IntCode is an exact wrapper around the repository's unbounded mathematical Int. Its intCodeValue
-- projection is a left inverse, hence the token transport is globally
-- injective (this is not a bounded machine-byte encoding).
canonicalTokenEncodeLeftInverse :
  ∀ token → intCodeValue (canonicalTokenEncode token) ＝ token
canonicalTokenEncodeLeftInverse token = refl

canonicalTokenEncodeInjective :
  ∀ {left right} →
  canonicalTokenEncode left ＝ canonicalTokenEncode right →
  left ＝ right
canonicalTokenEncodeInjective {left} {right} encodedEquality =
  trans
    (sym (canonicalTokenEncodeLeftInverse left))
    (trans
      (ap intCodeValue encodedEquality)
      (canonicalTokenEncodeLeftInverse right))

-- Any representation with an exact left inverse is globally injective.
-- If the inverse is also continuous, this algebraic fact remains true:
-- continuity is additional structure, not an extra premise needed for injectivity.
leftInverseImpliesInjective :
  ∀ {State Feature : Set}
  (observe : State → Feature)
  (inverse : Feature → State) →
  (∀ state → inverse (observe state) ＝ state) →
  ∀ {left right} → observe left ＝ observe right → left ＝ right
leftInverseImpliesInjective observe inverse leftInverse {left} {right} observationEquality =
  trans
    (sym (leftInverse left))
    (trans
      (ap inverse observationEquality)
      (leftInverse right))

canonicalTokenEncodeList : CanonicalTokenSequence → List IntCode
canonicalTokenEncodeList = map canonicalTokenEncode

canonicalTokenEncodeListLeftInverse :
  ∀ tokens → map intCodeValue (canonicalTokenEncodeList tokens) ＝ tokens
canonicalTokenEncodeListLeftInverse [] = refl
canonicalTokenEncodeListLeftInverse (token ∷ tokens) =
  ap (_∷_ token) (canonicalTokenEncodeListLeftInverse tokens)

canonicalTokenEncodeListInjective :
  ∀ {left right} →
  canonicalTokenEncodeList left ＝ canonicalTokenEncodeList right →
  left ＝ right
canonicalTokenEncodeListInjective {left} {right} encodedEquality =
  trans
    (sym (canonicalTokenEncodeListLeftInverse left))
    (trans
      (ap (map intCodeValue) encodedEquality)
      (canonicalTokenEncodeListLeftInverse right))

canonicalTokenStep : GRUState → CanonicalToken → GRUState
canonicalTokenStep s t = gruStep s (canonicalTokenEncode t)

canonicalTokenRecurrentNetwork :
  RecurrentNetwork GRUState CanonicalToken
canonicalTokenRecurrentNetwork =
  recurrentNetwork canonicalTokenStep

recurrentListState :
  ∀ {State Input : Set} →
  RecurrentNetwork State Input →
  List Input →
  State →
  State
recurrentListState R [] s = s
recurrentListState R (x ∷ xs) s =
  recurrentListState R xs (runNetwork R s x)

canonicalTokenListState :
  CanonicalTokenSequence →
  GRUState →
  GRUState
canonicalTokenListState [] s = s
canonicalTokenListState (t ∷ ts) s =
  canonicalTokenListState ts (canonicalTokenStep s t)

CanonicalTokenLogitVector : Set
CanonicalTokenLogitVector = CanonicalToken → IntCode

record CanonicalTokenLanguageModelKernel : Set₁ where
  constructor canonicalTokenLanguageModelKernel
  field
    logits : GRUState → CanonicalTokenLogitVector
open CanonicalTokenLanguageModelKernel public

canonicalTokenLogitTrace :
  CanonicalTokenLanguageModelKernel →
  CanonicalTokenSequence →
  GRUState →
  List CanonicalTokenLogitVector
canonicalTokenLogitTrace K [] s = []
canonicalTokenLogitTrace K (t ∷ ts) s =
  logits K s ∷
  canonicalTokenLogitTrace K ts (canonicalTokenStep s t)





------------------------------------------------------------------------
-- Computationally relevant policy boundary belongs beside the learner.
-- Beta is additive regret tolerance, not the layer-normalisation offset.
------------------------------------------------------------------------

module BetaOptimalityBoundary where
  open import Haskell.Prelude using (_≡_; refl)
  import Haskell.Prelude as HP

  BNat : Set
  BNat = HP.Nat

  bzero : BNat
  bzero = HP.zero

  bsuc : BNat → BNat
  bsuc = HP.suc

  BetaEmpty : Set
  BetaEmpty = HP.⊥

  data Action : Set where
    leftAction rightAction : Action

  data _≤B_ : BNat → BNat → Set where
    zeroLeB : {n : BNat} → _≤B_ bzero n
    succLeB : {m n : BNat} → _≤B_ m n → _≤B_ (bsuc m) (bsuc n)

  infixl 6 _+B_
  _+B_ : BNat → BNat → BNat
  HP.zero +B n = n
  HP.suc m +B n = HP.suc (m +B n)

  leTrans : {a b c : BNat} → _≤B_ a b → _≤B_ b c → _≤B_ a c
  leTrans zeroLeB _ = zeroLeB
  leTrans (succLeB first) (succLeB second) =
    succLeB (leTrans first second)

  leAddRight : (n beta : BNat) → _≤B_ n (n +B beta)
  leAddRight HP.zero beta = zeroLeB
  leAddRight (HP.suc n) beta = succLeB (leAddRight n beta)

  betaOptimal :
    BNat → (Action → BNat) → Action → Set
  betaOptimal beta reward choice =
    (alternative : Action) →
    _≤B_ (reward alternative) (reward choice +B beta)

  record ExactOptimalChoice (reward : Action → BNat) : Set where
    constructor exactOptimalChoice
    field
      selectedAction : Action
      selectedMaximal :
        (alternative : Action) →
        _≤B_ (reward alternative) (reward selectedAction)

  open ExactOptimalChoice public

  exactOptimalImpliesBetaOptimal :
    (beta : BNat)
    (reward : Action → BNat)
    (optimal : ExactOptimalChoice reward) →
    betaOptimal beta reward (selectedAction optimal)
  exactOptimalImpliesBetaOptimal beta reward optimal alternative =
    leTrans
      (selectedMaximal optimal alternative)
      (leAddRight (reward (selectedAction optimal)) beta)

  Not : Set → Set
  Not proposition = proposition → BetaEmpty

  counterReward : BNat → Action → Action → BNat
  counterReward beta leftAction leftAction = bzero
  counterReward beta leftAction rightAction = bsuc beta
  counterReward beta rightAction leftAction = bsuc beta
  counterReward beta rightAction rightAction = bzero

  noSuccessorBoundedBySelf : (n : BNat) → Not (_≤B_ (bsuc n) n)
  noSuccessorBoundedBySelf HP.zero ()
  noSuccessorBoundedBySelf (HP.suc n) (succLeB evidence) =
    noSuccessorBoundedBySelf n evidence

  noUniformBetaOptimalChoice :
    (beta : BNat) (choice : Action) →
    Not (betaOptimal beta (counterReward beta choice) choice)
  noUniformBetaOptimalChoice beta leftAction optimal =
    noSuccessorBoundedBySelf beta (optimal rightAction)
  noUniformBetaOptimalChoice beta rightAction optimal =
    noSuccessorBoundedBySelf beta (optimal leftAction)



------------------------------------------------------------------------
-- Tarski least-fixed-point theorem for an explicit Bellman contract.
-- No Bellman operator or monotonicity proof is postulated: each model must
-- supply its value order, arbitrary infima, and a proof of monotonicity.
------------------------------------------------------------------------

module CanonicalBellmanOrderTheory where
  open import Haskell.Prelude using (_≡_; refl; _×_; fst; snd)
  import Haskell.Prelude as HP

  BNat : Set
  BNat = HP.Nat

  bzero : BNat
  bzero = HP.zero

  bsuc : BNat → BNat
  bsuc = HP.suc

  -- Keep the extracted proof target self-contained: these helpers use
  -- Prelude equality, not the monolith's separate Haskell equality aliases.
  equalityTrans :
    {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  equalityTrans refl second = second

  equalitySym :
    {A : Set} {x y : A} → x ≡ y → y ≡ x
  equalitySym refl = refl

  equalityCong :
    {A B : Set} (f : A → B) {x y : A} →
    x ≡ y → f x ≡ f y
  equalityCong f refl = refl

  record CompleteMeetOrder (Value : Set) : Set₂ where
    field
      _⊑_ : Value → Value → Set
      refl⊑ : {x : Value} → x ⊑ x
      trans⊑ :
        {x y z : Value} → x ⊑ y → y ⊑ z → x ⊑ z
      antisym⊑ :
        {x y : Value} → x ⊑ y → y ⊑ x → x ≡ y
      infimum : (Value → Set) → Value
      infimumBelow :
        (P : Value → Set) → {x : Value} → P x → infimum P ⊑ x
      infimumGreatest :
        (P : Value → Set) → {z : Value} →
        (∀ {x : Value} → P x → z ⊑ x) → z ⊑ infimum P

  module FixedPoint {Value : Set} (L : CompleteMeetOrder Value) where
    open CompleteMeetOrder L

    preFixed : (Value → Value) → Value → Set
    preFixed F x = F x ⊑ x

    leastFixedPoint :
      (F : Value → Value) →
      (∀ {x y : Value} → x ⊑ y → F x ⊑ F y) →
      Value
    leastFixedPoint F mono = infimum (preFixed F)

    bellmanBelowLeast :
      (F : Value → Value)
      (mono : ∀ {x y : Value} → x ⊑ y → F x ⊑ F y) →
      F (leastFixedPoint F mono) ⊑ leastFixedPoint F mono
    bellmanBelowLeast F mono =
      infimumGreatest (preFixed F)
        (λ {x} px →
          trans⊑ (mono (infimumBelow (preFixed F) px)) px)

    leastBelowBellman :
      (F : Value → Value)
      (mono : ∀ {x y : Value} → x ⊑ y → F x ⊑ F y) →
      leastFixedPoint F mono ⊑ F (leastFixedPoint F mono)
    leastBelowBellman F mono =
      infimumBelow (preFixed F) (mono (bellmanBelowLeast F mono))

    leastFixedPointIsFixed :
      (F : Value → Value)
      (mono : ∀ {x y : Value} → x ⊑ y → F x ⊑ F y) →
      F (leastFixedPoint F mono) ≡ leastFixedPoint F mono
    leastFixedPointIsFixed F mono =
      antisym⊑ (bellmanBelowLeast F mono) (leastBelowBellman F mono)

    equalityImpliesOrder :
      {x y : Value} → x ≡ y → x ⊑ y
    equalityImpliesOrder refl = refl⊑

    leastFixedPointIsLeast :
      (F : Value → Value)
      (mono : ∀ {x y : Value} → x ⊑ y → F x ⊑ F y) →
      (x : Value) → F x ≡ x → leastFixedPoint F mono ⊑ x
    leastFixedPointIsLeast F mono x fixed =
      infimumBelow (preFixed F) (equalityImpliesOrder fixed)

  record BellmanSemantics (Value : Set) : Set₃ where
    constructor bellmanSemantics
    field
      valueOrder : CompleteMeetOrder Value
      bellmanOperator : Value → Value
      bellmanMonotone :
        {x y : Value} →
        CompleteMeetOrder._⊑_ valueOrder x y →
        CompleteMeetOrder._⊑_ valueOrder
          (bellmanOperator x) (bellmanOperator y)

  open BellmanSemantics public

  bellmanLeastFixedPoint :
    {Value : Set} →
    (B : BellmanSemantics Value) →
    Value
  bellmanLeastFixedPoint B =
    FixedPoint.leastFixedPoint
      (valueOrder B)
      (bellmanOperator B)
      (bellmanMonotone B)

  bellmanLeastFixedPointIsFixed :
    {Value : Set} →
    (B : BellmanSemantics Value) →
    bellmanOperator B (bellmanLeastFixedPoint B) ≡
      bellmanLeastFixedPoint B
  bellmanLeastFixedPointIsFixed B =
    FixedPoint.leastFixedPointIsFixed
      (valueOrder B)
      (bellmanOperator B)
      (bellmanMonotone B)

  bellmanLeastFixedPointIsLeast :
    {Value : Set} →
    (B : BellmanSemantics Value) →
    (x : Value) →
    bellmanOperator B x ≡ x →
    CompleteMeetOrder._⊑_ (valueOrder B) (bellmanLeastFixedPoint B) x
  bellmanLeastFixedPointIsLeast B x fixed =
    FixedPoint.leastFixedPointIsLeast
      (valueOrder B)
      (bellmanOperator B)
      (bellmanMonotone B)
      x
      fixed

  ------------------------------------------------------------------------
  -- Kleene's theorem for an omega-CPO and an omega-continuous Bellman map.
  -- This is deliberately a value-domain contract: learner-state transitions
  -- need not be fixed-point maps (the LCB count advances on every step).
  ------------------------------------------------------------------------

  infix 4 _⊑ω_

  record OmegaCPO (Value : Set) : Set₁ where
    field
      _⊑ω_ : Value → Value → Set
      reflω : {x : Value} → _⊑ω_ x x
      transω :
        {x y z : Value} → _⊑ω_ x y → _⊑ω_ y z → _⊑ω_ x z
      antisymω :
        {x y : Value} → _⊑ω_ x y → _⊑ω_ y x → x ≡ y
      bottomω : Value
      bottomLeastω : (x : Value) → _⊑ω_ bottomω x
      lubω :
        (xs : BNat → Value) →
        (∀ n → _⊑ω_ (xs n) (xs (bsuc n))) →
        Value
      lubUpperω :
        (xs : BNat → Value) →
        (chain : ∀ n → _⊑ω_ (xs n) (xs (bsuc n))) →
        (n : BNat) →
        _⊑ω_ (xs n) (lubω xs chain)
      lubLeastω :
        (xs : BNat → Value) →
        (chain : ∀ n → _⊑ω_ (xs n) (xs (bsuc n))) →
        (z : Value) →
        (∀ n → _⊑ω_ (xs n) z) →
        _⊑ω_ (lubω xs chain) z

  open OmegaCPO public

  record OmegaContinuousEndomap {Value : Set}
    (O : OmegaCPO Value) : Set₂ where
    field
      stepω : Value → Value
      monotoneω :
        {x y : Value} →
        OmegaCPO._⊑ω_ O x y →
        OmegaCPO._⊑ω_ O (stepω x) (stepω y)
      preservesOmegaSuprema :
        (xs : BNat → Value) →
        (chain : ∀ n → OmegaCPO._⊑ω_ O (xs n) (xs (bsuc n))) →
        stepω (OmegaCPO.lubω O xs chain) ≡
        OmegaCPO.lubω O
          (λ n → stepω (xs n))
          (λ n → monotoneω (chain n))

  module OmegaKleeneFixedPoint
    {Value : Set} (O : OmegaCPO Value) where
    iter : OmegaContinuousEndomap O → BNat → Value
    iter F HP.zero = OmegaCPO.bottomω O
    iter F (HP.suc n) =
      OmegaContinuousEndomap.stepω F (iter F n)

    iterChain :
      (F : OmegaContinuousEndomap O) →
      (n : BNat) →
      OmegaCPO._⊑ω_ O (iter F n) (iter F (bsuc n))
    iterChain F HP.zero =
      OmegaCPO.bottomLeastω O (OmegaContinuousEndomap.stepω F (iter F bzero))
    iterChain F (HP.suc n) =
      OmegaContinuousEndomap.monotoneω F (iterChain F n)

    leastFixedPoint :
      OmegaContinuousEndomap O → Value
    leastFixedPoint F = OmegaCPO.lubω O (iter F) (iterChain F)

    shiftUpper :
      (F : OmegaContinuousEndomap O) →
      (n : BNat) →
      OmegaCPO._⊑ω_ O (iter F n)
        (OmegaCPO.lubω O
          (λ k → iter F (bsuc k))
          (λ k → iterChain F (bsuc k)))
    shiftUpper F HP.zero =
      OmegaCPO.bottomLeastω O
        (OmegaCPO.lubω O
          (λ k → iter F (bsuc k))
          (λ k → iterChain F (bsuc k)))
    shiftUpper F (HP.suc n) =
      OmegaCPO.lubUpperω O
        (λ k → iter F (bsuc k))
        (λ k → iterChain F (bsuc k))
        n

    transEq :
      {x y z : Value} → x ≡ y → y ≡ z → x ≡ z
    transEq refl second = second

    symEq : {x y : Value} → x ≡ y → y ≡ x
    symEq refl = refl

    shiftedSupremum :
      (F : OmegaContinuousEndomap O) →
      leastFixedPoint F ≡
        OmegaCPO.lubω O
          (λ n → iter F (bsuc n))
          (λ n → iterChain F (bsuc n))
    shiftedSupremum F =
      OmegaCPO.antisymω O
        (OmegaCPO.lubLeastω O
          (iter F)
          (iterChain F)
          (OmegaCPO.lubω O
            (λ n → iter F (bsuc n))
            (λ n → iterChain F (bsuc n)))
          (shiftUpper F))
        (OmegaCPO.lubLeastω O
          (λ n → iter F (bsuc n))
          (λ n → iterChain F (bsuc n))
          (leastFixedPoint F)
          (λ n → OmegaCPO.lubUpperω O (iter F) (iterChain F) (bsuc n)))

    leastFixedPointIsFixed :
      (F : OmegaContinuousEndomap O) →
      OmegaContinuousEndomap.stepω F (leastFixedPoint F) ≡
        leastFixedPoint F
    leastFixedPointIsFixed F =
      transEq
        (OmegaContinuousEndomap.preservesOmegaSuprema F (iter F) (iterChain F))
        (symEq (shiftedSupremum F))

    equalityToOrder :
      {x y : Value} → x ≡ y → OmegaCPO._⊑ω_ O x y
    equalityToOrder refl = OmegaCPO.reflω O

    iterBelowFixed :
      (F : OmegaContinuousEndomap O) →
      (x : Value) →
      OmegaContinuousEndomap.stepω F x ≡ x →
      (n : BNat) →
      OmegaCPO._⊑ω_ O (iter F n) x
    iterBelowFixed F x fixed HP.zero = OmegaCPO.bottomLeastω O x
    iterBelowFixed F x fixed (HP.suc n) =
      OmegaCPO.transω O
        (OmegaContinuousEndomap.monotoneω F
          (iterBelowFixed F x fixed n))
        (equalityToOrder fixed)

    leastFixedPointIsLeast :
      (F : OmegaContinuousEndomap O) →
      (x : Value) →
      OmegaContinuousEndomap.stepω F x ≡ x →
      OmegaCPO._⊑ω_ O (leastFixedPoint F) x
    leastFixedPointIsLeast F x fixed =
      OmegaCPO.lubLeastω O
        (iter F)
        (iterChain F)
        x
        (iterBelowFixed F x fixed)

    leastFixedPointUnique :
      (F : OmegaContinuousEndomap O) →
      (x : Value) →
      (fixed : OmegaContinuousEndomap.stepω F x ≡ x) →
      (∀ {y : Value} →
        OmegaContinuousEndomap.stepω F y ≡ y →
        OmegaCPO._⊑ω_ O x y) →
      x ≡ leastFixedPoint F
    leastFixedPointUnique F x fixed least =
      OmegaCPO.antisymω O
        (least {y = leastFixedPoint F}
          (leastFixedPointIsFixed F))
        (leastFixedPointIsLeast F x fixed)

  record OmegaContinuousBellmanSemantics (Value : Set) : Set₃ where
    constructor omegaContinuousBellmanSemantics
    field
      valueDomain : OmegaCPO Value
      bellmanOperator : OmegaContinuousEndomap valueDomain

  open OmegaContinuousBellmanSemantics public

  bellmanStreamValue :
    {Value : Set} →
    (B : OmegaContinuousBellmanSemantics Value) →
    BNat →
    Value
  bellmanStreamValue B =
    OmegaKleeneFixedPoint.iter
      (valueDomain B) (bellmanOperator B)

  bellmanStreamLeastFixedPoint :
    {Value : Set} →
    (B : OmegaContinuousBellmanSemantics Value) →
    Value
  bellmanStreamLeastFixedPoint B =
    OmegaKleeneFixedPoint.leastFixedPoint
      (valueDomain B) (bellmanOperator B)

  bellmanStreamLeastFixedPointAtZero :
    {Value : Set} →
    (B : OmegaContinuousBellmanSemantics Value) →
    bellmanStreamValue B bzero ≡
      OmegaCPO.bottomω (valueDomain B)
  bellmanStreamLeastFixedPointAtZero B = refl

  bellmanStreamLeastFixedPointIsFixed :
    {Value : Set} →
    (B : OmegaContinuousBellmanSemantics Value) →
    OmegaContinuousEndomap.stepω (bellmanOperator B)
      (bellmanStreamLeastFixedPoint B) ≡
      bellmanStreamLeastFixedPoint B
  bellmanStreamLeastFixedPointIsFixed B =
    OmegaKleeneFixedPoint.leastFixedPointIsFixed
      (valueDomain B) (bellmanOperator B)

  bellmanStreamLeastFixedPointIsLeast :
    {Value : Set} →
    (B : OmegaContinuousBellmanSemantics Value) →
    (x : Value) →
    OmegaContinuousEndomap.stepω (bellmanOperator B) x ≡ x →
    OmegaCPO._⊑ω_ (valueDomain B)
      (bellmanStreamLeastFixedPoint B) x
  bellmanStreamLeastFixedPointIsLeast B x fixed =
    OmegaKleeneFixedPoint.leastFixedPointIsLeast
      (valueDomain B) (bellmanOperator B) x fixed

  bellmanStreamLeastFixedPointUnique :
    {Value : Set} →
    (B : OmegaContinuousBellmanSemantics Value) →
    (x : Value) →
    (fixed : OmegaContinuousEndomap.stepω (bellmanOperator B) x ≡ x) →
    (∀ {y : Value} →
      OmegaContinuousEndomap.stepω (bellmanOperator B) y ≡ y →
      OmegaCPO._⊑ω_ (valueDomain B) x y) →
    x ≡ bellmanStreamLeastFixedPoint B
  bellmanStreamLeastFixedPointUnique B x fixed least =
    OmegaKleeneFixedPoint.leastFixedPointUnique
      (valueDomain B) (bellmanOperator B) x fixed least





  ------------------------------------------------------------------------
  -- Neural-network / MDP instantiation of the omega-Kleene theorem.
  --
  -- State-value functions form the value domain. Reward and expected
  -- transition value define one-step action returns; the least upper bound
  -- over actions defines the optimal Bellman backup. A Q network and greedy
  -- policy are explicit model fields, so neural assumptions remain visible.
  -- State/action spaces are ordinary types: no Fin or Vec encoding needed.
  ------------------------------------------------------------------------

  record NeuralPolicyMDP : Set₄ where
    constructor neuralPolicyMDP
    field
      neuralState : Set
      neuralAction : Set
      neuralScalar : Set
      neuralParameters : Set

      mdpScalarDomain : OmegaCPO neuralScalar
      mdpValueDomain : OmegaCPO (neuralState → neuralScalar)

      mdpDiscount : neuralScalar
      mdpAdd : neuralScalar → neuralScalar → neuralScalar
      mdpMultiply : neuralScalar → neuralScalar → neuralScalar
      mdpReward : neuralState → neuralAction → neuralScalar
      mdpTransitionExpectation :
        neuralState →
        neuralAction →
        (neuralState → neuralScalar) →
        neuralScalar

      -- This is the least upper bound over action values.
      mdpBestActionValue :
        neuralState → (neuralAction → neuralScalar) → neuralScalar
      mdpBestActionUpper :
        (state : neuralState) →
        (actionValues : neuralAction → neuralScalar) →
        (action : neuralAction) →
        OmegaCPO._⊑ω_ mdpScalarDomain
          (actionValues action)
          (mdpBestActionValue state actionValues)
      mdpBestActionLeast :
        (state : neuralState) →
        (actionValues : neuralAction → neuralScalar) →
        (bound : neuralScalar) →
        (∀ action →
          OmegaCPO._⊑ω_ mdpScalarDomain (actionValues action) bound) →
        OmegaCPO._⊑ω_ mdpScalarDomain
          (mdpBestActionValue state actionValues) bound

      -- Neural Q approximation, its selected parameter state, and a greedy policy.
      nnQ :
        neuralParameters → neuralState → neuralAction → neuralScalar
      nnParameters : neuralParameters
      nnGreedyPolicy : neuralState → neuralAction
      nnGreedy :
        (state : neuralState) →
        (action : neuralAction) →
        OmegaCPO._⊑ω_ mdpScalarDomain
          (nnQ nnParameters state action)
          (nnQ nnParameters state (nnGreedyPolicy state))

      -- The Bellman map preserves suprema of increasing omega-chains. Its
      -- equation identifies the map with reward + discounted expectation,
      -- followed by the action supremum.
      mdpBellmanEndomap : OmegaContinuousEndomap mdpValueDomain
      mdpBellmanEquation :
        (values : neuralState → neuralScalar) →
        (state : neuralState) →
        OmegaContinuousEndomap.stepω mdpBellmanEndomap values state ≡
          mdpBestActionValue state
            (λ action →
              mdpAdd
                (mdpReward state action)
                (mdpMultiply mdpDiscount
                  (mdpTransitionExpectation state action values)))

  open NeuralPolicyMDP public

  -- Expected discounted one-step return for state, action, and continuation values.
  neuralActionReturn :
    (M : NeuralPolicyMDP) →
    (neuralState M → neuralScalar M) →
    neuralState M →
    neuralAction M →
    neuralScalar M
  neuralActionReturn M values state action =
    mdpAdd M
      (mdpReward M state action)
      (mdpMultiply M (mdpDiscount M)
        (mdpTransitionExpectation M state action values))

  -- Value iteration uses index zero for bottom and applies the Bellman map
  -- once per successor index.
  neuralBellmanValueIteration :
    (M : NeuralPolicyMDP) →
    BNat →
    neuralState M →
    neuralScalar M
  neuralBellmanValueIteration M n state =
    OmegaKleeneFixedPoint.iter
      (mdpValueDomain M)
      (mdpBellmanEndomap M)
      n
      state

  -- Supremum of bottom-starting Bellman iterates: the MDP optimal value function.
  neuralBellmanOptimalValueFunction :
    (M : NeuralPolicyMDP) →
    neuralState M → neuralScalar M
  neuralBellmanOptimalValueFunction M =
    OmegaKleeneFixedPoint.leastFixedPoint
      (mdpValueDomain M)
      (mdpBellmanEndomap M)

  neuralBellmanAtStepZero :
    (M : NeuralPolicyMDP) →
    (state : neuralState M) →
    neuralBellmanValueIteration M bzero state ≡
      OmegaCPO.bottomω (mdpValueDomain M) state
  neuralBellmanAtStepZero M state = refl

  neuralBellmanOptimalValueIsFixed :
    (M : NeuralPolicyMDP) →
    OmegaContinuousEndomap.stepω (mdpBellmanEndomap M)
      (neuralBellmanOptimalValueFunction M) ≡
      neuralBellmanOptimalValueFunction M
  neuralBellmanOptimalValueIsFixed M =
    OmegaKleeneFixedPoint.leastFixedPointIsFixed
      (mdpValueDomain M)
      (mdpBellmanEndomap M)

  neuralBellmanOptimalValueIsLeast :
    (M : NeuralPolicyMDP) →
    (candidate : neuralState M → neuralScalar M) →
    OmegaContinuousEndomap.stepω (mdpBellmanEndomap M) candidate ≡ candidate →
    OmegaCPO._⊑ω_ (mdpValueDomain M)
      (neuralBellmanOptimalValueFunction M) candidate
  neuralBellmanOptimalValueIsLeast M candidate fixed =
    OmegaKleeneFixedPoint.leastFixedPointIsLeast
      (mdpValueDomain M)
      (mdpBellmanEndomap M)
      candidate
      fixed

  -- Q* is the exact Bellman return computed from V*: reward plus discounted
  -- transition expectation. It is a value-domain object, not a graph-search
  -- heuristic or the capability planner's proposal prior.
  neuralBellmanQStar :
    (M : NeuralPolicyMDP) →
    neuralState M →
    neuralAction M →
    neuralScalar M
  neuralBellmanQStar M state action =
    neuralActionReturn M
      (neuralBellmanOptimalValueFunction M)
      state action

  -- The optimal value at each state is the least upper bound of its Q* action
  -- values. This is the explicit V*=sup_a Q* bridge for this MDP contract.
  neuralBellmanValueIsSupremumOfQStar :
    (M : NeuralPolicyMDP) →
    (state : neuralState M) →
    neuralBellmanOptimalValueFunction M state ≡
      mdpBestActionValue M state (neuralBellmanQStar M state)
  neuralBellmanValueIsSupremumOfQStar M state =
    equalityTrans
      (equalitySym (equalityCong (λ values → values state)
        (neuralBellmanOptimalValueIsFixed M)))
      (mdpBellmanEquation M
        (neuralBellmanOptimalValueFunction M)
        state)

  -- Equality transports action values into the scalar order.
  scalarEqualityImpliesOrder :
    (M : NeuralPolicyMDP) →
    {left right : neuralScalar M} →
    left ≡ right →
    OmegaCPO._⊑ω_ (mdpScalarDomain M) left right
  scalarEqualityImpliesOrder M refl =
    OmegaCPO.reflω (mdpScalarDomain M)

  -- With exact Bellman-consistent Q values, a network-greedy action is
  -- maximal for one-step optimal Bellman return. This is local action
  -- optimality; global policy optimality additionally needs the policy-value
  -- evaluation theorem (e.g. discounted contraction/uniqueness assumptions).
  neuralPolicyGreedyOptimalAtBellmanValue :
    (M : NeuralPolicyMDP) →
    (exactQ :
      (state : neuralState M) →
      (action : neuralAction M) →
      nnQ M (nnParameters M) state action ≡
        neuralBellmanQStar M state action) →
    (state : neuralState M) →
    (action : neuralAction M) →
    OmegaCPO._⊑ω_ (mdpScalarDomain M)
      (neuralActionReturn M
        (neuralBellmanOptimalValueFunction M) state action)
      (neuralActionReturn M
        (neuralBellmanOptimalValueFunction M)
        state (nnGreedyPolicy M state))
  neuralPolicyGreedyOptimalAtBellmanValue M exactQ state action =
    OmegaCPO.transω (mdpScalarDomain M)
      (scalarEqualityImpliesOrder M
        (OmegaKleeneFixedPoint.symEq (mdpScalarDomain M) (exactQ state action)))
      (OmegaCPO.transω (mdpScalarDomain M)
        (nnGreedy M state action)
        (scalarEqualityImpliesOrder M
          (exactQ state (nnGreedyPolicy M state))))

  ------------------------------------------------------------------------
  -- Quantified approximation guarantee for the Q*-greedy policy.
  --
  -- If the fixed network approximates each target Q* action value from both
  -- sides within epsilon, and the scalar addition is monotone in its left
  -- argument, then a greedy network action is within 2 epsilon of every
  -- action in the target ordering. This is conditional on the supplied
  -- uniform-error witness; it does not claim that this architecture satisfies
  -- a universal approximation theorem or that training constructs the witness.
  ------------------------------------------------------------------------

  neuralPolicyGreedyTwoEpsilonRegret :
    (M : NeuralPolicyMDP) →
    (epsilon : neuralScalar M) →
    (addMonotoneRight :
      {x y z : neuralScalar M} →
      OmegaCPO._⊑ω_ (mdpScalarDomain M) x y →
      OmegaCPO._⊑ω_ (mdpScalarDomain M)
        (mdpAdd M x z) (mdpAdd M y z)) →
    (uniformQApproximation :
      (state : neuralState M) →
      (action : neuralAction M) →
      (OmegaCPO._⊑ω_ (mdpScalarDomain M)
        (neuralBellmanQStar M state action)
        (mdpAdd M (nnQ M (nnParameters M) state action) epsilon)
      ×
      OmegaCPO._⊑ω_ (mdpScalarDomain M)
        (nnQ M (nnParameters M) state action)
        (mdpAdd M (neuralBellmanQStar M state action) epsilon))) →
    (state : neuralState M) →
    (action : neuralAction M) →
    OmegaCPO._⊑ω_ (mdpScalarDomain M)
      (neuralBellmanQStar M state action)
      (mdpAdd M
        (mdpAdd M
          (neuralBellmanQStar M state (nnGreedyPolicy M state))
          epsilon)
        epsilon)
  neuralPolicyGreedyTwoEpsilonRegret
    M epsilon addMonotoneRight uniformQApproximation state action =
      OmegaCPO.transω (mdpScalarDomain M)
        (fst (uniformQApproximation state action))
        (OmegaCPO.transω (mdpScalarDomain M)
          (addMonotoneRight (nnGreedy M state action))
          (addMonotoneRight
            (snd
              (uniformQApproximation
                state (nnGreedyPolicy M state)))))

