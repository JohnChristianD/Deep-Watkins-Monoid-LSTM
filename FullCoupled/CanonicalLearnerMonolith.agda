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
--polarity
--large-indices
--no-forced-argument-recursion
--with-K
--no-guardedness
--cohesion
--exact-split
--injective-type-constructors
#-}

------------------------------------------------------------------------
-- Canonical learner semantics.
--
-- RUSS assurance boundary: the computational functions below give explicit
-- finite operational interpretations where stated; they do not turn the postulated
-- Markov/ECT0/Prop-choice basis into a derived theorem. The independent consistency
-- of this basis together with the theorem monolith, Reflection/TC primitives, rewrite
-- system, and full imports remains unproved. See docs/russ-computational-interpretation-and-consistency.md.
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
open import Haskell.Prelude public
open import Haskell.Prim public using (pos; negsuc)
open import Haskell.Law.Ord.Ordering public
open import Haskell.Law.Equality public
open import Haskell.Law.Functor.FromMonad public
open import Haskell.Law.Semigroup.List public
open import Haskell.Law.Nat public
open import Haskell.Law.Num.Nat public using (addNat-idʳ; addNat-suc)
{-# REWRITE addNat-idʳ addNat-suc #-}
open import Haskell.Law.Monad.List public
open import Haskell.Law.Monoid.List public
open import Haskell.Prim.Absurd public
open import Haskell.Prim.Applicative public
open import Haskell.Extra.Delay public
open import Haskell.Extra.Erase public
open import Haskell.Extra.Refinement public
open import Haskell.Control.Exception public
open import Agda.Primitive public

-- Preserve the file's established fullwidth equality notation as a purely
-- definitional alias of Prelude propositional equality. No new axiom or
-- extensionality principle is introduced by this compatibility name.
infix 4 _＝_
_＝_ : ∀ {ℓ : Level} {A : Set ℓ} → A → A → Set ℓ
_＝_ = _≡_

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
  open import Haskell.Prelude using (Nat; Integer; zero; suc; Bool; True; False; List; []; _∷_; _≡_; refl)

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

  -- A nontrivial constructive witness tying the operational evaluator
  -- to the finite-trace relation used by the ECT₀ signature: increment
  -- register zero, jump to the halt instruction, and exhibit output one.
  machineIncrementTrace :
    ComputationTrace
      (incrementRegister zero (suc zero) ∷ haltInstruction ∷ [])
      zero (suc zero)
  machineIncrementTrace = record
    { finalMachineState =
        machineConfiguration (suc zero)
          (updateRegister zero (suc zero) (initialRegisters zero))
    ; machineTrace =
        machineStepsCons
          (incrementStep
            {pc = zero}
            {register = zero}
            {target = suc zero}
            {store = initialRegisters zero}
            refl)
          machineStepsRefl
    ; machineTraceHalted =
        machineHalted
          {pc = suc zero}
          {store = updateRegister zero (suc zero) (initialRegisters zero)}
          refl
    ; machineTraceOutput = refl
    }

  -- A total, fuel-bounded operational evaluator for the explicit register
  -- machine. Its result distinguishes a halt observation from fuel exhaustion.
  -- Exhaustion is inconclusive; only a halt plus a valid ComputationTrace
  -- certifies a completed computation.
  data MachineRunResult : Set where
    machineRunHalted : MachineConfiguration → MachineRunResult
    machineRunFuelExhausted : MachineConfiguration → MachineRunResult

  runMachineFuel :
    (fuel : Nat) →
    (program : RecursiveProgram) →
    MachineConfiguration →
    MachineRunResult
  runMachineFuel zero program configuration =
    machineRunFuelExhausted configuration
  runMachineFuel (suc fuel) program (machineConfiguration pc store)
    with lookupInstruction program pc
  ... | haltInstruction = machineRunHalted (machineConfiguration pc store)
  ... | incrementRegister register target =
    runMachineFuel fuel program
      (machineConfiguration target
        (updateRegister register (suc (store register)) store))
  ... | decrementOrJump register onZero onPositive with store register
  ...   | zero =
    runMachineFuel fuel program
      (machineConfiguration onZero store)
  ...   | suc value =
    runMachineFuel fuel program
      (machineConfiguration onPositive
        (updateRegister register value store))

  runMachineWithFuel :
    Nat → RecursiveProgram → Nat → MachineRunResult
  runMachineWithFuel fuel program input =
    runMachineFuel fuel program (initialConfiguration input)

  machineRunRegisterZero : MachineRunResult → Nat
  machineRunRegisterZero (machineRunHalted (machineConfiguration pc store)) =
    store zero
  machineRunRegisterZero (machineRunFuelExhausted (machineConfiguration pc store)) =
    store zero

  machineIncrementOutputRegression :
    machineRunRegisterZero
      (runMachineWithFuel
        (suc (suc zero))
        (incrementRegister zero (suc zero) ∷ haltInstruction ∷ [])
        zero)
    ≡ suc zero
  machineIncrementOutputRegression = refl

  machineHaltRegression :
    runMachineWithFuel
      (suc zero)
      (haltInstruction ∷ [])
      (suc zero)
    ≡ machineRunHalted (initialConfiguration (suc zero))
  machineHaltRegression = refl

  machineFuelExhaustionRegression : Bool
  machineFuelExhaustionRegression with
    runMachineWithFuel
      (suc zero)
      (incrementRegister zero zero ∷ [])
      zero
  ... | machineRunHalted _ = False
  ... | machineRunFuelExhausted _ = True

  machineFuelExhaustionRegressionChecked :
    machineFuelExhaustionRegression ≡ True
  machineFuelExhaustionRegressionChecked = refl

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
  -- Russian constructivism: one explicit assumption package, with public
  -- projections. These declarations are assumptions, not REWRITE rules.
  ----------------------------------------------------------------------

  -- This record is the visible RUSS trust boundary for this development.
  -- It packages Markov's Principle for decidable predicates, the concrete
  -- finite-register-machine ECT₀ signature below, and Prop-valued countable
  -- choice. Public projections expose the assumptions to downstream proofs;
  -- that API visibility does not make them rewrite rules or derive them from
  -- MLTT.
  --
  -- CONSISTENCY STATUS: neither this record nor a successful Agda kernel
  -- check certifies joint RUSS consistency. Type-checking establishes
  -- well-typedness only relative to this postulate, the imported theory,
  -- rewrite configuration, compiler primitives, and trusted checker. A
  -- consistency claim needs a model or relative-consistency argument for this
  -- exact signature and its complete transitive dependency closure. Searching
  -- for an inhabitant of an empty type is not such an argument.
  --
  -- FORMALIZATION BOUNDARY: the project-specific ECT₀ signature must not be
  -- identified with a textbook formulation until the computation relation,
  -- admissible predicates, and quantifiers are shown equivalent. Its
  -- computational content is a substantive assumption. The Prop-valued
  -- countable-choice field is a further project assumption; its compatibility
  -- with the chosen RUSS model must be justified independently.
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
  mapFunction g h : (x : A) → P x
  k l mNat n   : Nat
  xs ys zs    : List A

transport : (P : A → Set ℓ) → x ≡ y → P x → P y
transport P refl p = p

+comm : mNat + n ≡ n + mNat
+comm {mNat = zero}  = refl
+comm {mNat = suc m} = cong suc (+comm {mNat = m})

zero+ : zero + n ≡ n
zero+ = refl

suc+ : (suc mNat) + n ≡ suc (mNat + n)
suc+ = refl


canonical-map-identity : map (λ x → x) xs ≡ xs
canonical-map-identity {xs = []}     = refl
canonical-map-identity {xs = x ∷ xs} = cong (_∷_ x) canonical-map-identity

map-fuse : map mapFunction (map g xs) ≡ map (λ x → mapFunction (g x)) xs
map-fuse {xs = []}     = refl
map-fuse {xs = x ∷ xs} = cong (_∷_ _) map-fuse

canonical-map-append : map mapFunction (xs ++ ys) ≡ (map mapFunction xs) ++ (map mapFunction ys)
canonical-map-append {xs = []}     = refl
canonical-map-append {xs = x ∷ xs} = cong (_∷_ _) (canonical-map-append {xs = xs})

{-# REWRITE canonical-map-identity map-fuse canonical-map-append #-}

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


-- The pinned Agda2HS integer-law module contains a Nat/Num inference
-- failure in subtraction-times-multiplication. Keep the needed constructive
-- proofs local to the canonical monolith, and state that boundary with primitive
-- Nat arithmetic rather than importing the failing module.
module CanonicalIntegerLaws where
  
  open import Haskell.Prim
  open import Haskell.Prim.Num
  open import Haskell.Prim.Integer
  
  open import Haskell.Law.Equality
  open import Haskell.Law.Num.Def
  open import Haskell.Law.Num.Nat
  
  -- Open the internal definitions because
  -- these must be transparent for proofs.
  open Haskell.Prim.Integer.Internal
  
  addInteger-idˡ : ∀ (x : Integer) → 0 + x ≡ x
  addInteger-idˡ (pos _)    = refl
  addInteger-idˡ (negsuc _) = cong negsuc refl
  
  addInteger-idʳ : ∀ (x : Integer) → x + 0 ≡ x
  addInteger-idʳ (pos n)    = cong pos    $ addNat-idʳ n
  addInteger-idʳ (negsuc _) = cong negsuc refl
  
  mulInteger-idˡ : ∀ (x : Integer) → 1 * x ≡ x
  mulInteger-idˡ (pos x)    = cong pos    (addNat-idʳ x)
  mulInteger-idˡ (negsuc x) = cong negsuc (addNat-idʳ x)
  
  mulInteger-idʳ : ∀ (x : Integer) → x * 1 ≡ x
  mulInteger-idʳ (pos x)    = cong pos    (mulNat-idʳ x)
  mulInteger-idʳ (negsuc x) = cong negsuc (mulNat-idʳ x)
  
  subNat-refl : ∀ (x : Nat) → subNat x x ≡ 0
  subNat-refl zero    = refl
  subNat-refl (suc x) = subNat-refl x
  
  n-n≡0-Nat : ∀ (x y : Nat) → subNat (x + y) x ≡ pos y
  n-n≡0-Nat x       zero    rewrite addNat-idʳ x = subNat-refl x
  n-n≡0-Nat zero    (suc _) = refl
  n-n≡0-Nat (suc x) (suc y) = n-n≡0-Nat x (suc y)
  
  n-n≡0-Integer : ∀ (x : Integer) → x + (negateInteger x) ≡ 0
  n-n≡0-Integer (pos zero)    = refl
  n-n≡0-Integer (pos (suc x)) = subNat-refl x
  n-n≡0-Integer (negsuc x)    = subNat-refl x
  
  mulInteger-zeroˡ : ∀ (x : Integer) → 0 * x ≡ 0
  mulInteger-zeroˡ (pos _)    = refl
  mulInteger-zeroˡ (negsuc _) = refl
  
  mulInteger-zeroʳ : ∀ (x : Integer) → x * 0 ≡ 0
  mulInteger-zeroʳ (pos n)    = cong pos (mulNat-zeroʳ n)
  mulInteger-zeroʳ (negsuc n) rewrite mulNat-zeroʳ n = refl
  
  addInteger-comm : ∀ (x y : Integer) → x + y ≡ y + x
  addInteger-comm (pos x)    (pos y)    = cong pos (addNat-comm x y)
  addInteger-comm (pos _)    (negsuc _) = refl
  addInteger-comm (negsuc _) (pos _)    = refl
  addInteger-comm (negsuc x) (negsuc y) = cong negsuc (cong suc (addNat-comm x y))
  
  subNat|x-[y+z]≡x-y-z : ∀ (x y z : Nat) → subNat x (y + suc z) ≡ subNat x y + negsuc z
  subNat|x-[y+z]≡x-y-z _       zero    _ = refl
  subNat|x-[y+z]≡x-y-z zero    (suc y) z = cong negsuc (addNat-suc y z)
  subNat|x-[y+z]≡x-y-z (suc x) (suc y) z = subNat|x-[y+z]≡x-y-z x y z
  
  subNat|x-y+z≡[x+z]-y : ∀ (x y z : Nat) → subNat x y + pos (suc z) ≡ subNat (x + suc z) y
  subNat|x-y+z≡[x+z]-y _       zero    _ = refl
  subNat|x-y+z≡[x+z]-y zero    (suc _) _ = refl
  subNat|x-y+z≡[x+z]-y (suc x) (suc y) z = subNat|x-y+z≡[x+z]-y x y z
  
  subNat-cong-suc : ∀ (x y : Nat) → subNat (suc x) y ≡ pos 1 + subNat x y
  subNat-cong-suc _       zero    = refl
  subNat-cong-suc zero    (suc _) = refl
  subNat-cong-suc (suc x) (suc y) = subNat-cong-suc x y
  
  subNat|x+[y-z]≡[1+x]+[y-[1+z]] : ∀ (x y z : Nat) → pos x + subNat y z ≡ pos (suc x) + subNat y (suc z)
  subNat|x+[y-z]≡[1+x]+[y-[1+z]] x zero    zero    = cong pos (addNat-idʳ x)
  subNat|x+[y-z]≡[1+x]+[y-[1+z]] x (suc y) zero    = cong pos (addNat-suc x y)
  subNat|x+[y-z]≡[1+x]+[y-[1+z]] _ zero    (suc _) = refl
  subNat|x+[y-z]≡[1+x]+[y-[1+z]] x (suc y) (suc z) = subNat|x+[y-z]≡[1+x]+[y-[1+z]] x y z
  
  subNat|x-y+[1+z]≡[1+x]+[z-y] : ∀ (x y z : Nat) → subNat x y + pos (suc z) ≡ pos (suc x) + subNat z y
  subNat|x-y+[1+z]≡[1+x]+[z-y] x       zero    z    = cong pos (addNat-suc x z)
  subNat|x-y+[1+z]≡[1+x]+[z-y] zero    (suc _) zero = refl
  subNat|x-y+[1+z]≡[1+x]+[z-y] zero    (suc y) (suc z) = subNat-cong-suc z y
  subNat|x-y+[1+z]≡[1+x]+[z-y] (suc x) (suc y) z       =
    subNat x y + pos (suc z)             ≡⟨ subNat|x-y+[1+z]≡[1+x]+[z-y] x y z ⟩
    pos (suc x)       + subNat z y       ≡⟨ subNat|x+[y-z]≡[1+x]+[y-[1+z]] (suc x) z y ⟩
    pos (suc (suc x)) + subNat z (suc y) ∎
  
  subNat|[1+x+y]-z≡[1+x]+[y-z] : ∀ (x y z : Nat) → subNat (suc x + y) z ≡ pos (suc x) + subNat y z
  subNat|[1+x+y]-z≡[1+x]+[y-z] _ _       zero    = refl
  subNat|[1+x+y]-z≡[1+x]+[y-z] x zero    (suc z) = cong (λ eq → subNat eq z) (addNat-idʳ x)
  subNat|[1+x+y]-z≡[1+x]+[y-z] x (suc y) (suc z) =
    subNat (x + suc y) z     ≡⟨ sym (subNat|x-y+z≡[x+z]-y x z y) ⟩
    subNat x z + pos (suc y) ≡⟨ subNat|x-y+[1+z]≡[1+x]+[z-y] x z y ⟩
    pos (suc x) + subNat y z ∎
  
  subNat|x-y+[-[1+z]]≡x-z+[-[1+y]] : ∀ (x y z : Nat) → subNat x y + negsuc z ≡ subNat x z + negsuc y
  subNat|x-y+[-[1+z]]≡x-z+[-[1+y]] x y z = begin
    subNat x y + negsuc z ≡⟨ sym (subNat|x-[y+z]≡x-y-z x y z) ⟩
    subNat x (y + suc z)  ≡⟨ cong (subNat x) (addNat-comm y (suc z)) ⟩
    subNat x (suc z + y)  ≡⟨ cong (subNat x) (sym (addNat-suc z y)) ⟩
    subNat x (z + suc y)  ≡⟨ subNat|x-[y+z]≡x-y-z x z y ⟩
    subNat x z + negsuc y ∎
  
  subNat-cong-+ : ∀ (x y z : Nat) → subNat (x + y) (x + z) ≡ subNat y z
  subNat-cong-+ x       y zero rewrite addNat-idʳ x = n-n≡0-Nat x y
  subNat-cong-+ zero    _ (suc _) = refl
  subNat-cong-+ (suc x) y (suc z) = subNat-cong-+ x y (suc z)
  
  -- Use primitive natural arithmetic here. The generic Num instance
  -- leaves metas in the pinned upstream proof at this exact reduction boundary.
  subNat-cong-addNat : ∀ (x y z : Nat) → subNat (addNat x y) (addNat x z) ≡ subNat y z
  subNat-cong-addNat zero y z = refl
  subNat-cong-addNat (suc x) y z = subNat-cong-addNat x y z
  
  subNat-distrib-minus :
    ∀ (m n o : Nat) →
    subNat n o * pos m ≡ subNat (mulNat n m) (mulNat o m)
  subNat-distrib-minus _ _ zero = refl
  subNat-distrib-minus zero zero (suc o)
    rewrite mulNat-zeroʳ o = refl
  subNat-distrib-minus (suc _) zero (suc _) = refl
  subNat-distrib-minus zero (suc n) (suc o)
    rewrite mulNat-zeroʳ o
          | mulInteger-zeroʳ (subNat n o)
          | mulNat-zeroʳ n = refl
  subNat-distrib-minus (suc m) (suc n) (suc o) =
    subNat n o * pos (suc m)
      ≡⟨ subNat-distrib-minus (suc m) n o ⟩
    subNat (mulNat n (suc m)) (mulNat o (suc m))
      ≡⟨ sym (subNat-cong-addNat m (mulNat n (suc m)) (mulNat o (suc m))) ⟩
    subNat
      (addNat m (mulNat n (suc m)))
      (addNat m (mulNat o (suc m))) ∎
  
  subNat-mult-flip-negsuc : ∀ (m n o : Nat) → subNat o n * negsuc m ≡ subNat n o * pos (suc m)
  subNat-mult-flip-negsuc _ zero    zero    = refl
  subNat-mult-flip-negsuc _ zero    (suc _) = refl
  subNat-mult-flip-negsuc _ (suc _) zero    = refl
  subNat-mult-flip-negsuc m (suc n) (suc o) = subNat-mult-flip-negsuc m n o
  
  subNat-distrib-minus-cong-+ :
    ∀ (m n o : Nat) →
    subNat o n * pos (suc m) ≡
    subNat (addNat m (mulNat o (suc m)))
           (addNat m (mulNat n (suc m)))
  subNat-distrib-minus-cong-+ m n o =
    subNat o n * pos (suc m)
      ≡⟨ subNat-distrib-minus (suc m) o n ⟩
    subNat (mulNat o (suc m)) (mulNat n (suc m))
      ≡⟨ sym (subNat-cong-addNat m (mulNat o (suc m)) (mulNat n (suc m))) ⟩
    subNat (addNat m (mulNat o (suc m)))
           (addNat m (mulNat n (suc m))) ∎
  
  
  addInteger-assoc : ∀ (x y z : Integer) → (x + y) + z ≡ x + (y + z)
  addInteger-assoc (pos zero) j k rewrite addInteger-idˡ      j  | addInteger-idˡ (j + k) = refl
  addInteger-assoc i (pos zero) k rewrite addInteger-idʳ  i      | addInteger-idˡ      k  = refl
  addInteger-assoc i j (pos zero) rewrite addInteger-idʳ (i + j) | addInteger-idʳ  j      = refl
  addInteger-assoc (negsuc m) (negsuc n) (pos (suc o)) =
    (negsuc m + negsuc n) + pos (suc o)       ≡⟨⟩
    negsuc (suc (m + n)) + pos (suc o)        ≡⟨⟩
    subNat o (suc m + n)                      ≡⟨ cong (subNat o) (addNat-comm (suc m) n) ⟩
    subNat o (n + suc m)                      ≡⟨ subNat|x-[y+z]≡x-y-z o n m ⟩
    subNat o n + negsuc m                     ≡⟨ addInteger-comm (subNat o n) (negsuc m) ⟩
    negsuc m + subNat o n                     ≡⟨⟩
    negsuc m + (negsuc n + pos (suc o))       ∎
  addInteger-assoc (negsuc m) (pos (suc n)) (pos (suc o)) =
    (negsuc m + pos (suc n)) + pos (suc o)    ≡⟨⟩
    subNat n m + pos (suc o)                  ≡⟨ subNat|x-y+z≡[x+z]-y n m o ⟩
    subNat (n + suc o) m                      ≡⟨⟩
    negsuc m + pos (suc (n + suc o))          ≡⟨⟩
    negsuc m + (pos (suc n) + pos (suc o))    ∎
  addInteger-assoc (pos (suc m)) (negsuc n) (negsuc o) =
    (pos (suc m) + negsuc n) + negsuc o       ≡⟨⟩
    subNat m n + negsuc o                     ≡⟨ sym $ subNat|x-[y+z]≡x-y-z m n o ⟩
    subNat m (n + suc o)                      ≡⟨ cong (subNat m) (addNat-suc n o) ⟩
    subNat m (suc (n + o))                    ≡⟨⟩
    pos (suc m) + (negsuc (suc (n + o)))      ≡⟨⟩
    pos (suc m) + (negsuc n + negsuc o)       ∎
  addInteger-assoc (pos (suc m)) (negsuc n) (pos (suc o)) =
    (pos (suc m) + negsuc n) + pos (suc o)    ≡⟨⟩
    subNat m n + pos (suc o)                  ≡⟨ subNat|x-y+[1+z]≡[1+x]+[z-y] m n o ⟩
    pos (suc m) + subNat o n                  ≡⟨⟩
    pos (suc m) + (negsuc n + pos (suc o))    ∎
  addInteger-assoc (pos (suc x)) (pos (suc y)) (negsuc z) = begin
    (pos (suc x) + pos (suc y)) + negsuc z    ≡⟨⟩
    pos (suc (x + (suc y))) + negsuc z        ≡⟨ cong (_+ negsuc z) (cong pos (cong suc (addNat-suc x y))) ⟩
    pos (suc (suc (x + y))) + negsuc z        ≡⟨⟩
    subNat (suc (x + y)) z                    ≡⟨⟩
    subNat (suc  x + y)  z                    ≡⟨ subNat|[1+x+y]-z≡[1+x]+[y-z] x y z ⟩
    pos (suc x) + subNat y z                  ≡⟨⟩
    pos (suc x) + (pos (suc y)   + negsuc z)  ∎
  addInteger-assoc (negsuc m) (negsuc n) (negsuc o) = cong negsuc $ cong suc $
    suc ((m + n) + o)                         ≡⟨ cong suc (addNat-assoc m n o) ⟩
    suc (m + (n + o))                         ≡⟨ sym (addNat-suc m (n + o)) ⟩
    m + (suc (n + o))                         ∎
  addInteger-assoc (negsuc m) (pos (suc n)) (negsuc o) =
    (negsuc m + pos (suc n)) + negsuc o       ≡⟨⟩
    subNat n m + negsuc o                     ≡⟨ subNat|x-y+[-[1+z]]≡x-z+[-[1+y]] n m o ⟩
    subNat n o + negsuc m                     ≡⟨ addInteger-comm (subNat n o) (negsuc m) ⟩
    negsuc m + subNat n o                     ≡⟨⟩
    negsuc m + (pos (suc n) - pos (suc o))    ∎
  addInteger-assoc (pos (suc m)) (pos (suc n)) (pos (suc o)) = cong pos (addNat-assoc (suc m) (suc n) (suc o))
  
  distribute-1ˡ : ∀ (x y : Nat) → x * (1 + y) ≡ x + (y * x)
  distribute-1ˡ x y = begin
    x * (suc y) ≡⟨ mulNat-suc x y ⟩
    x + (x * y) ≡⟨ cong (x +_) (mulNat-comm x y) ⟩
    x + (y * x) ∎
  
  mulInteger-comm : ∀ (x y : Integer) → x * y ≡ y * x
  mulInteger-comm (pos x)    (pos y)    = cong pos (mulNat-comm x y)
  mulInteger-comm (pos x)    (negsuc y) = cong negNat $       distribute-1ˡ x y
  mulInteger-comm (negsuc x) (pos y)    = cong negNat $ sym $ distribute-1ˡ y x
  mulInteger-comm (negsuc x) (negsuc y) = cong pos $ cong suc $
    y + (x * (suc y)) ≡⟨ cong (y +_) (distribute-1ˡ x y) ⟩
    y + (x + (y * x)) ≡⟨ cong (y +_) (cong (x +_) (mulNat-comm y x)) ⟩
    y + (x + (x * y)) ≡⟨ sym (addNat-assoc y x (x * y)) ⟩
    (y + x) + (x * y) ≡⟨ cong (_+ x * y) (addNat-comm y x) ⟩
    (x + y) + (x * y) ≡⟨ addNat-assoc x y (x * y) ⟩
    x + (y + (x * y)) ≡⟨ cong (x +_) (sym (distribute-1ˡ y x)) ⟩
    x + (y * (suc x)) ∎
  
  distrib-lemma : ∀ (m n o : Nat) → suc (m + ((n + o) * suc m)) ≡ (n * suc m) + (suc (m + (o * suc m)))
  distrib-lemma m n o =
    suc (m + ((n + o) * suc m))             ≡⟨ cong suc (cong (m +_) (mulNat-distributeʳ-addNat (suc m) n o)) ⟩
    suc (m + ((n * suc m)   + (o * suc m))) ≡⟨⟩
     suc m + ((n * suc m)   + (o * suc m))  ≡⟨ sym (addNat-assoc (suc m) (n * suc m) (o * suc m) ) ⟩
    (suc m +  (n * suc m))  + (o * suc m)   ≡⟨ cong (_+ o * suc m) (addNat-comm (suc m) (n * suc m)) ⟩
    ((n * suc m) +  suc  m) + (o * suc m)   ≡⟨ addNat-assoc (n * suc m) (suc m) (o * suc m) ⟩
     (n * suc m) + (suc (m  + (o * suc m))) ∎
  
  distrib-lemma2 : ∀ (m n o : Nat) → m + ((n * suc m) + (suc m + (o * suc m))) ≡ suc ((m + (n * suc m)) + (m + (o * suc m)))
  distrib-lemma2 m n o =
     m + (    (n * suc m) + (suc  m + (o * suc m))) ≡⟨⟩
     m + (    (n * suc m) +  suc (m + (o * suc m))) ≡⟨ sym (addNat-assoc m (n * suc m) (suc (m + (o * suc m)))) ⟩
    (m +      (n * suc m)) + suc (m + (o * suc m))  ≡⟨ addNat-suc (m + (n * suc m)) (m + (o * suc m)) ⟩
    suc ((m + (n * suc m)) +     (m + (o * suc m))) ∎
  
  mulInteger-distributeʳ-addInteger : ∀ (x y z : Integer) → (y + z) * x ≡ (y * x) + (z * x)
  mulInteger-distributeʳ-addInteger (pos zero) j k rewrite mulInteger-zeroʳ j | mulInteger-zeroʳ k | mulInteger-zeroʳ (j + k) = refl
  mulInteger-distributeʳ-addInteger i (pos zero) k rewrite addInteger-idˡ k   | mulInteger-zeroˡ i | addInteger-idˡ   (k * i) = refl
  mulInteger-distributeʳ-addInteger i j (pos zero) rewrite addInteger-idʳ j   | mulInteger-zeroˡ i | addInteger-idʳ   (j * i) = refl
  mulInteger-distributeʳ-addInteger (negsuc m)    (negsuc n)    (pos (suc o)) = begin
    subNat o n * negsuc m                      ≡⟨ subNat-mult-flip-negsuc m n o ⟩
    subNat n o * pos (suc m)                   ≡⟨ subNat-distrib-minus-cong-+ m o n ⟩
    subNat (m + (n * suc m)) (m + (o * suc m)) ∎
  mulInteger-distributeʳ-addInteger (negsuc m)    (pos (suc n)) (pos (suc o)) = cong negsuc $ begin
    m + ((n + suc o) * suc m)                       ≡⟨ cong (m +_) (mulNat-distributeʳ-addNat (suc m) n (suc o)) ⟩
    m + (     (n * suc m) + (suc m + (o * suc m)))  ≡⟨ distrib-lemma2 m n o ⟩
    suc ((m + (n * suc m)) +     (m + (o * suc m))) ∎ -- Y
  mulInteger-distributeʳ-addInteger (pos (suc m)) (negsuc n)    (negsuc o)    = cong negsuc $ begin
    m + (suc (m + ((n + o) * suc m)))               ≡⟨⟩
    m + (suc m  + ((n + o) * suc m))                ≡⟨ cong (m +_) (distrib-lemma m n o) ⟩
    m + (     (n * suc m) + (suc m + (o * suc m)))  ≡⟨ distrib-lemma2 m n o ⟩
    suc ((m + (n * suc m)) + (m + (o * suc m)))     ∎ -- Y
  mulInteger-distributeʳ-addInteger (pos (suc m)) (negsuc n)    (pos (suc o)) = subNat-distrib-minus-cong-+ m n o
  mulInteger-distributeʳ-addInteger (pos (suc m)) (pos (suc n)) (negsuc o)    = subNat-distrib-minus-cong-+ m o n
  mulInteger-distributeʳ-addInteger (negsuc m)    (negsuc n)    (negsuc o)    = cong pos $ cong suc $
    m + (suc (m + ((n + o) * suc m)))           ≡⟨⟩
    m + (suc m  + ((n + o) * suc m))            ≡⟨ cong (m +_) (distrib-lemma m n o) ⟩
    m + ((n * suc m) + (suc m  + (o * suc m)))  ≡⟨ sym (addNat-assoc m (n * suc m) (suc m + (o * suc m))) ⟩
    (m + (n * suc m)) + (suc (m + (o * suc m))) ∎ -- X
  mulInteger-distributeʳ-addInteger (negsuc m)    (pos (suc n)) (negsuc o)    =
    subNat n o * negsuc m                      ≡⟨ subNat-mult-flip-negsuc m o n ⟩
    subNat o n * pos (suc m)                   ≡⟨ subNat-distrib-minus-cong-+ m n o ⟩
    subNat (m + (o * suc m)) (m + (n * suc m)) ∎
  mulInteger-distributeʳ-addInteger (pos (suc m)) (pos (suc n)) (pos (suc o)) = cong pos $ cong suc $
    m + ((n + suc o) * suc m)                   ≡⟨ cong (m +_) (mulNat-distributeʳ-addNat (suc m) n (suc o)) ⟩
    m + ((n * suc m) + (suc m  + (o * suc m)))  ≡⟨ sym (addNat-assoc m (n * suc m) (suc m + (o * suc m))) ⟩
    (m + (n * suc m)) + (suc m  + (o * suc m))  ≡⟨⟩
    (m + (n * suc m)) + (suc (m + (o * suc m))) ∎ -- X
  
  mulInteger-distributeˡ-addInteger : ∀ (x y z : Integer) → x * (y + z) ≡ (x * y) + (x * z)
  mulInteger-distributeˡ-addInteger x y z
    -- This proof works the very same as addNat-distributeˡ-mulNat.
    rewrite (mulInteger-comm x (y + z)) -- makes or goal become: (y + z) * x ≡ (x * y) + (x * z)
    rewrite (mulInteger-comm x y)       -- makes or goal become: (y + z) * x ≡ (y * x) + (x * z)
    rewrite (mulInteger-comm x z)       -- makes or goal become: (y + z) * x ≡ (y * x) + (z * x)
    = mulInteger-distributeʳ-addInteger x y z
  
  mulInteger-assoc-lemma-2 : ∀ (m n o : Nat) → (n + m * suc n) * suc o ≡ (n * suc o) + (m * suc (o + (n * suc o)))
  mulInteger-assoc-lemma-2 m n o =            begin
    (n + (m * suc n)) * (suc o)               ≡⟨ mulNat-distributeʳ-addNat (suc o) n (m * suc n) ⟩
    (n * (suc o)) + ((m * suc n) * (suc o))   ≡⟨ cong (n * suc o +_) (mulNat-assoc m (suc n) (suc o)) ⟩
    (n * suc o) + (m * suc (o + (n * suc o))) ∎
  
  mulInteger-assoc-lemma : ∀ (m n o : Nat)
    → o + ((n + m * suc n) * suc o) ≡ (o + (n * suc o)) + (m * suc (o + (n * suc o)))
  mulInteger-assoc-lemma m n o =                      begin
      o + ((n + m * suc n) * suc o)                   ≡⟨ cong (o +_) (mulInteger-assoc-lemma-2 m n o) ⟩
      o + ((n * suc o) + (m * suc (o + (n * suc o)))) ≡⟨ sym (addNat-assoc o (n * suc o) (m * suc (o + (n * suc o)))) ⟩
      (o + (n * suc o)) + (m * suc (o + (n * suc o))) ∎
  
  mulInteger-assoc : ∀ (x y z : Integer) → (x * y) * z ≡ x * (y * z)
  mulInteger-assoc (pos zero) j k rewrite mulInteger-zeroˡ j | mulInteger-zeroˡ k | mulInteger-zeroˡ (j * k) = refl
  mulInteger-assoc i (pos zero) k rewrite mulInteger-zeroʳ i | mulInteger-zeroˡ k | mulInteger-zeroʳ i       = refl
  mulInteger-assoc i j (pos zero) rewrite mulInteger-zeroʳ j | mulInteger-zeroʳ i | mulInteger-zeroʳ (i * j) = refl
  mulInteger-assoc (negsuc m)    (negsuc n)    (pos (suc o)) = cong pos (cong suc (mulInteger-assoc-lemma m n o))
  mulInteger-assoc (negsuc m)    (pos (suc n)) (pos (suc o)) = cong negsuc        (mulInteger-assoc-lemma m n o)
  mulInteger-assoc (pos (suc m)) (negsuc n)    (negsuc o)    = cong pos (cong suc (mulInteger-assoc-lemma m n o))
  mulInteger-assoc (pos (suc m)) (negsuc n)    (pos (suc o)) = cong negsuc        (mulInteger-assoc-lemma m n o)
  mulInteger-assoc (pos (suc m)) (pos (suc n)) (negsuc o)    = cong negsuc        (mulInteger-assoc-lemma m n o)
  mulInteger-assoc (negsuc m)    (negsuc n)    (negsuc o)    = cong negsuc        (mulInteger-assoc-lemma m n o)
  mulInteger-assoc (negsuc m)    (pos (suc n)) (negsuc o)    = cong pos (cong suc (mulInteger-assoc-lemma m n o))
  mulInteger-assoc (pos (suc m)) (pos (suc n)) (pos (suc o)) = cong pos (cong suc (mulInteger-assoc-lemma m n o))
  
  instance
    iLawfulNumInteger : IsLawfulNum Integer
    iLawfulNumInteger .IsLawfulNum.+-assoc = addInteger-assoc
    iLawfulNumInteger .IsLawfulNum.+-comm = addInteger-comm
    iLawfulNumInteger .IsLawfulNum.+-idˡ x = addInteger-idˡ x
    iLawfulNumInteger .IsLawfulNum.+-idʳ x = addInteger-idʳ x
    iLawfulNumInteger .IsLawfulNum.neg-inv x = n-n≡0-Integer x
    iLawfulNumInteger .IsLawfulNum.*-assoc = mulInteger-assoc
    iLawfulNumInteger .IsLawfulNum.*-idˡ x = mulInteger-idˡ x
    iLawfulNumInteger .IsLawfulNum.*-idʳ x = mulInteger-idʳ x
    iLawfulNumInteger .IsLawfulNum.distributeˡ = mulInteger-distributeˡ-addInteger
    iLawfulNumInteger .IsLawfulNum.distributeʳ = mulInteger-distributeʳ-addInteger
  
open CanonicalIntegerLaws public using
  ( addInteger-idˡ
  ; addInteger-idʳ
  ; addInteger-assoc
  ; mulInteger-idˡ
  ; mulInteger-idʳ
  ; mulInteger-zeroˡ
  ; mulInteger-zeroʳ
  ; mulInteger-distributeˡ-addInteger
  ; mulInteger-assoc
  )

-- The learner's older mathematical notation is mapped onto the official
-- Agda2HS Prelude types. Keep this compatibility layer local: no extra
-- Agda monolith or third-party theory is introduced.
ℕ : Set
ℕ = Nat


infix 4 _<ℕ_
data _<ℕ_ : ℕ → ℕ → Set where
  natLtZeroSucc : ∀ {n} → zero <ℕ suc n
  natLtStep : ∀ {m n} → m <ℕ n → suc m <ℕ suc n

not-less-than-itself : (n : ℕ) → n <ℕ n → ⊥
not-less-than-itself zero ()
not-less-than-itself (suc n) (natLtStep smaller) =
  not-less-than-itself n smaller



plus-zero : ∀ n → n + zero ＝ n
plus-zero zero = refl
plus-zero (suc n) = cong suc (plus-zero n)

plus-succ : ∀ (m n : ℕ) → m + suc n ＝ suc (m + n)
plus-succ zero n = refl
plus-succ (suc m) n = refl

plus-succ-lt : ∀ (m n : ℕ) → m <ℕ (m + suc n)
plus-succ-lt zero n = natLtZeroSucc
plus-succ-lt (suc m) n = natLtStep (plus-succ-lt m n)

plus-succ-not-self : ∀ (m n : ℕ) → m + suc n ≠ m
plus-succ-not-self m n eq =
  not-less-than-itself m (transport (λ z → m <ℕ z) eq (plus-succ-lt m n))

succ-succ-lt : ∀ (n : ℕ) → n <ℕ suc (suc n)
succ-succ-lt zero = natLtZeroSucc
succ-succ-lt (suc n) = natLtStep (succ-succ-lt n)

succ-succ-not-self : ∀ n → suc (suc n) ≠ n
succ-succ-not-self n eq =
  not-less-than-itself (suc (suc n))
    (transport (λ z → z <ℕ suc (suc n)) (sym eq) (succ-succ-lt n))

iterate : ∀ {S : Set} → (S → S) → ℕ → S → S
iterate step zero s = s
iterate step (suc n) s = step (iterate step n s)

OrbitNonFixed : ∀ {S : Set} {step : S → S} → S → Set
OrbitNonFixed {step = step} s = ∀ n → iterate step n s ≠ step (iterate step n s)

data Signed : Set where
  signedNeg : ℕ → Signed
  signedZer : Signed
  signedPos : ℕ → Signed

signedCode : Integer → Signed
signedCode (pos 0) = signedZer
signedCode (pos (suc n)) = signedPos (suc n)
signedCode (negsuc n) = signedNeg (suc n)

data BoolLike : Set where
  enabled disabled : BoolLike

record ActionSpace (A : Set) : Set where
  constructor actionSpace
  field
    candidates : List ℕ
    witness : ℕ
open ActionSpace public

QFunction : ∀ {A : Set} → Set
QFunction {A} = ℕ → Integer

CountFunction : ∀ {A : Set} → Set
CountFunction {A} = ℕ → ℕ

zeroQ : ∀ {A : Set} → QFunction {A}
zeroQ _ = 0

zeroCounts : ∀ {A : Set} → CountFunction {A}
zeroCounts _ = zero

natEq : ℕ → ℕ → BoolLike
natEq zero zero = enabled
natEq zero (suc n) = disabled
natEq (suc m) zero = disabled
natEq (suc m) (suc n) = natEq m n

natLt : ℕ → ℕ → BoolLike
natLt zero zero = disabled
natLt zero (suc n) = enabled
natLt (suc m) zero = disabled
natLt (suc m) (suc n) = natLt m n

natLE : ℕ → ℕ → BoolLike
natLE zero n = enabled
natLE (suc m) zero = disabled
natLE (suc m) (suc n) = natLE m n

maxNat : ℕ → ℕ → ℕ
maxNat zero n = n
maxNat (suc m) zero = suc m
maxNat (suc m) (suc n) = suc (maxNat m n)

updateAt : ∀ {A : Set} → QFunction {A} → ℕ → Integer → QFunction {A}
updateAt q a r i with natEq i a
... | enabled = (_+_) (q i) r
... | disabled = q i

incAt : ∀ {A : Set} → CountFunction {A} → ℕ → CountFunction {A}
incAt c a i with natEq i a
... | enabled = suc (c i)
... | disabled = c i

record CriticState (A : Set) : Set where
  constructor criticState
  field values : QFunction {A}
open CriticState public

record WatkinsKernel (A : Set) : Set₁ where
  constructor mkWatkinsKernel
  field
    updateCritic : CriticState A → Integer → CriticState A
    greedy : CriticState A → Integer → BoolLike
    traceUpdate : BoolLike → BoolLike → BoolLike
open WatkinsKernel public

record WatkinsState (A : Set) : Set where
  constructor watkinsState
  field critic : CriticState A
        signal : Integer
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
  field bonus : ℕ → Integer
open LCBCountKernel public

finiteLCBBonus8 : ℕ → Integer
finiteLCBBonus8 zero = fromNat 127
finiteLCBBonus8 (suc zero) = fromNat 63
finiteLCBBonus8 (suc (suc zero)) = fromNat 31
finiteLCBBonus8 (suc (suc (suc zero))) = fromNat 15
finiteLCBBonus8 (suc (suc (suc (suc zero)))) = fromNat 7
finiteLCBBonus8 (suc (suc (suc (suc (suc zero))))) = fromNat 3
finiteLCBBonus8 (suc (suc (suc (suc (suc (suc zero)))))) = fromNat 1
finiteLCBBonus8 _ = 0

lcbNegate : Integer → Integer
lcbNegate x = negateInteger x

scoreA : ∀ {A : Set} → QFunction {A} → CountFunction {A} → ℕ → Integer
scoreA q c a = (_+_) (q a) (lcbNegate (finiteLCBBonus8 (c a)))

lcbScore : ∀ {A : Set} → LCBCountKernel → LCBCountState A → CriticState A → QFunction {A}
lcbScore L c q a = (_+_) (values q a) (lcbNegate (bonus L (valuesCount c a)))

sparsemaxTemperature : ℕ
sparsemaxTemperature = 16

ScoreEntry : Set
ScoreEntry = Integer × ℕ

scoreList : ∀ {A : Set} → ActionSpace A → QFunction {A} → CountFunction {A} → List ScoreEntry
scoreList {A} K q c = map (λ a → (scoreA {A = A} q c a , a)) (candidates K)

data ComparisonResult : Set where
  less equal greater : ComparisonResult

compareInt8 : Integer → Integer → ComparisonResult
compareInt8 x y with compare (x) (y)
... | LT = less
... | EQ = equal
... | GT = greater

compareNat : ℕ → ℕ → ComparisonResult
compareNat zero zero = equal
compareNat zero (suc _) = less
compareNat (suc _) zero = greater
compareNat (suc m) (suc n) = compareNat m n

scoreBefore : ScoreEntry → ScoreEntry → Bool
scoreBefore (s₁ , a₁) (s₂ , a₂) with compareInt8 s₁ s₂
... | less = False
... | greater = True
... | equal with compareNat a₁ a₂
... | less = False
... | equal = True
... | greater = True

insertScore : ScoreEntry → List ScoreEntry → List ScoreEntry
insertScore x [] = x ∷ []
insertScore x (y ∷ ys) with scoreBefore x y
... | True = x ∷ y ∷ ys
... | False = y ∷ insertScore x ys

sortScores : List ScoreEntry → List ScoreEntry
sortScores [] = []
sortScores (x ∷ xs) = insertScore x (sortScores xs)

natAt : ℕ → List ℕ → ℕ
natAt k [] = zero
natAt zero (x ∷ xs) = x
natAt (suc k) (x ∷ xs) = natAt k xs

sumList : List ℕ → ℕ
sumList [] = zero
sumList (x ∷ xs) = x + sumList xs

------------------------------------------------------------------------
-- Integer LayerNorm kernel.
--
-- This kernel operates directly on Agda2HS Prelude Integer, not a machine byte.  The normalization arithmetic therefore
-- remains integral and the normalized output is represented as an exact
-- integer ratio.  A certificate supplies the non-zero square root of
-- the integer radicand; no floating-point approximation enters the
-- proof surface.
------------------------------------------------------------------------

integerCodeSum : List Integer → Integer
integerCodeSum [] = pos 0
integerCodeSum (x ∷ xs) = x + integerCodeSum xs

integerCodeSumList : List Integer → Integer
integerCodeSumList [] = pos 0
integerCodeSumList (x ∷ xs) = x + integerCodeSumList xs

integerLayerNormCenteredNumerator :
  List Integer → Integer → Integer
integerLayerNormCenteredNumerator xs x =
  (pos (length xs)) * x + negateInteger (integerCodeSum xs)

integerLayerNormCenteredNumerators :
  List Integer → List Integer
integerLayerNormCenteredNumerators xs =
  map
    (λ x → integerLayerNormCenteredNumerator xs x)
    xs

integerLayerNormSquare : Integer → Integer
integerLayerNormSquare z = z * z

integerLayerNormVarianceNumerator :
  List Integer → Integer
integerLayerNormVarianceNumerator xs =
  integerCodeSumList
    (map
      integerLayerNormSquare
      (integerLayerNormCenteredNumerators xs))

integerLayerNormEpsilonContribution :
  List Integer → ℕ → Integer
integerLayerNormEpsilonContribution xs epsilon =
  (_*_)
      (fromNat epsilon)
      ((_*_) (fromNat (length xs)) (fromNat (length xs)))

integerLayerNormRadicand :
  List Integer → ℕ → Integer
integerLayerNormRadicand xs epsilon =
  integerLayerNormVarianceNumerator xs
  +
  integerLayerNormEpsilonContribution xs epsilon

record IntegerLayerNormConfig : Set where
  constructor integerLayerNormConfig
  field fixedScale gamma beta : Integer
open IntegerLayerNormConfig public

record IntegerLayerNormCertificate
  (xs : List Integer) : Set where
  constructor integerLayerNormCertificate
  field
    epsilon : ℕ
    root : ℕ
    rootSquared :
      (_*_) (fromNat root) (fromNat root) ＝
      integerLayerNormRadicand xs epsilon
    rootNonZero : root ≠ zero
open IntegerLayerNormCertificate public

record IntegerLayerNormValue : Set where
  constructor mkIntegerLayerNormValue
  field
    numerator : Integer
    denominator : ℕ
    denominatorNonZero : denominator ≠ zero
open IntegerLayerNormValue public

integerLayerNormValue :
  ∀ {xs : List Integer} →
  IntegerLayerNormConfig →
  IntegerLayerNormCertificate xs →
  Integer →
  IntegerLayerNormValue
integerLayerNormValue {xs} config certificate x =
  mkIntegerLayerNormValue
    (gamma config *
      (fixedScale config *
        integerLayerNormCenteredNumerator xs x)
     +
     (beta config * (pos (root certificate))))
    (root certificate)
    (rootNonZero certificate)


intCodeMagnitude : Integer → ℕ
intCodeMagnitude (pos n) = n
intCodeMagnitude (negsuc n) = suc n

infixl 6 _∸_
_∸_ : ℕ → ℕ → ℕ
zero ∸ n = zero
suc m ∸ zero = suc m
suc m ∸ suc n = m ∸ n

topCodes : ℕ → List ScoreEntry → List ℕ
topCodes zero xs = []
topCodes (suc k) [] = []
topCodes (suc k) ((x , a) ∷ xs) = intCodeMagnitude x ∷ topCodes k xs

-- Natural-number arithmetic aliases stay local so calculations use this
-- module's single ℕ source type throughout.
infixl 7 _*ℕ_
_*ℕ_ : ℕ → ℕ → ℕ
x *ℕ zero = zero
x *ℕ suc y = x + x *ℕ y

infixl 6 _+ℕ_
_+ℕ_ : ℕ → ℕ → ℕ
_+ℕ_ = _+_

supportValid : List ScoreEntry → ℕ → ℕ → BoolLike
supportValid xs temperature k with natLt (sumList (topCodes k xs)) (((k *ℕ natAt (k ∸ 1) (topCodes k xs)) +ℕ temperature))
... | enabled = enabled
... | disabled = disabled

searchSupport : List ScoreEntry → ℕ → ℕ → ℕ → ℕ → ℕ
searchSupport xs temperature zero current best = best
searchSupport xs temperature (suc n) current best with supportValid xs temperature current
... | enabled = searchSupport xs temperature n (suc current) (maxNat best current)
... | disabled = searchSupport xs temperature n (suc current) best

supportSize : ∀ {A : Set} → ActionSpace A → QFunction {A} → CountFunction {A} → ℕ
supportSize K q c = searchSupport (sortScores (scoreList K q c)) sparsemaxTemperature (length (candidates K)) (suc zero) (suc zero)

record SparseWeight : Set where
  constructor sparseWeight
  field numerator denominator : ℕ
open SparseWeight public

sparsemaxWeight : ∀ {A : Set} → ActionSpace A → QFunction {A} → CountFunction {A} → ℕ → SparseWeight
sparsemaxWeight {A} K q c a = sparseWeight (((supportK *ℕ intCodeMagnitude (scoreA {A = A} q c a)) +ℕ sparsemaxTemperature) ∸ scoreSum) (supportK *ℕ sparsemaxTemperature)
  where
    scoreEntries = sortScores (scoreList K q c)
    supportK = supportSize K q c
    scoreSum = sumList (topCodes supportK scoreEntries)

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
  lcbCountState (incAt {A = A} counts a) (suc total)

------------------------------------------------------------------------
-- Agda2HS Prelude does not expose Rational. Keep an exact executable
-- rational code: a signed Integer numerator and denominator-minus-one.
-- The denominator is positive by construction because it is recovered with
-- suc; denominator zero is not representable. Codes are not gcd-normalized,
-- and code equality is not equality of mathematical fractions.
------------------------------------------------------------------------

RationalCode : Set
RationalCode = Integer × ℕ

fromNatRationalCode : ℕ → ℕ → RationalCode
fromNatRationalCode n denominatorMinusOne =
  pos n , denominatorMinusOne

rationalCodeNumerator : RationalCode → Integer
rationalCodeNumerator (numerator , _) = numerator

rationalCodeNumeratorMagnitude : RationalCode → ℕ
rationalCodeNumeratorMagnitude (pos n , _) = n
rationalCodeNumeratorMagnitude (negsuc n , _) = suc n

rationalCodeDenominator : RationalCode → ℕ
rationalCodeDenominator (_ , denominatorMinusOne) =
  suc denominatorMinusOne

rationalCodeCrossProductEqual : RationalCode → RationalCode → Set
rationalCodeCrossProductEqual
  (leftNumerator , leftDenominatorMinusOne)
  (rightNumerator , rightDenominatorMinusOne) =
  (leftNumerator * pos (suc rightDenominatorMinusOne)) ＝
  (rightNumerator * pos (suc leftDenominatorMinusOne))


-- Exact arithmetic on positive-denominator fraction codes. Codes are not
-- normalized: operations preserve the represented value, not unique syntax.
rationalCodeAdd : RationalCode → RationalCode → RationalCode
rationalCodeAdd
  (leftNumerator , leftDenominatorMinusOne)
  (rightNumerator , rightDenominatorMinusOne) =
  ( leftNumerator * pos (suc rightDenominatorMinusOne)
      + rightNumerator * pos (suc leftDenominatorMinusOne)
  , leftDenominatorMinusOne * rightDenominatorMinusOne
      + leftDenominatorMinusOne
      + rightDenominatorMinusOne
  )

rationalCodeMultiply : RationalCode → RationalCode → RationalCode
rationalCodeMultiply
  (leftNumerator , leftDenominatorMinusOne)
  (rightNumerator , rightDenominatorMinusOne) =
  ( leftNumerator * rightNumerator
  , leftDenominatorMinusOne * rightDenominatorMinusOne
      + leftDenominatorMinusOne
      + rightDenominatorMinusOne
  )

rationalCodeAddThirdsRegression :
  rationalCodeCrossProductEqual
    (rationalCodeAdd (fromNatRationalCode 1 2) (fromNatRationalCode 1 2))
    (fromNatRationalCode 2 2)
rationalCodeAddThirdsRegression = refl

rationalCodeMultiplyThirdHalfRegression :
  rationalCodeCrossProductEqual
    (rationalCodeMultiply (fromNatRationalCode 1 2) (fromNatRationalCode 1 1))
    (fromNatRationalCode 1 5)
rationalCodeMultiplyThirdHalfRegression = refl


-- Total quotient/remainder by a positive natural. Structural
-- recursion on the numerator keeps this evaluator accepted by Agda's
-- termination checker; divisor zero has explicit total behavior.
fractionDivision : ℕ → ℕ → ℕ × ℕ
fractionDivision _ zero = zero , zero
fractionDivision zero (suc _) = zero , zero
fractionDivision (suc n) (suc d)
  with fractionDivision n (suc d)
... | quotient , remainder with natEq (suc remainder) (suc d)
...   | enabled = suc quotient , zero
...   | disabled = quotient , suc remainder

rationalCodeDivideMagnitude : ℕ → RationalCode → ℕ
rationalCodeDivideMagnitude n (_ , denominatorMinusOne) =
  fst (fractionDivision n (suc denominatorMinusOne))

qLog8 : Integer → RationalCode
qLog8 x with intCodeMagnitude x
... | zero = fromNatRationalCode 1 zero
... | suc n = fromNatRationalCode (128 ∸ suc n) (suc n)

munchausenScale8 : ℕ
munchausenScale8 = 16

signedRationalCodeBias8 : RationalCode → Integer
signedRationalCodeBias8 q with rationalCodeNumeratorMagnitude q
... | zero = 0
... | suc n = negateInteger
  (fromNat
    (rationalCodeDivideMagnitude
      (munchausenScale8 *ℕ suc n)
      q))

qLog2Bias8 : Integer → Integer
qLog2Bias8 x =
  signedRationalCodeBias8 (qLog8 x)

negativeAlpha8 : Integer
negativeAlpha8 = fromNat 255

record SignedQLogControl : Set where
  constructor signedQLogControl
  field mode coefficient : Integer
open SignedQLogControl public

canonicalQLogControl : SignedQLogControl
canonicalQLogControl =
  signedQLogControl negativeAlpha8 negativeAlpha8

qLogSignal : SignedQLogControl → Integer → Integer
qLogSignal c x = (_+_) x (coefficient c)

data HardSign : Set where
  negativeSign zeroSign positiveSign : HardSign

hardSignNonnegative : Integer → HardSign
hardSignNonnegative (pos 0) = zeroSign
hardSignNonnegative (pos (suc n)) = positiveSign
hardSignNonnegative (negsuc n) = negativeSign

hardSign : Integer → HardSign
hardSign (pos 0) = zeroSign
hardSign (pos (suc n)) = positiveSign
hardSign (negsuc n) = negativeSign

hardSignGate : Integer → Integer
hardSignGate x with hardSign x
... | negativeSign = fromNat 255
... | zeroSign = 0
... | positive = 1

two8 : Integer
two8 = (_+_) 1 1

relu8 : Integer → Integer
relu8 x with hardSign x
... | negativeSign = 0
... | zeroSign = 0
... | positive = x

leaky2 : Integer → Integer
leaky2 x with hardSign x
... | negativeSign = (_*_) two8 x
... | zeroSign = 0
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
  field matrixZ matrixR matrixH : Integer
open MonoidLSTMMatrices public

record MonoidLSTMNoise : Set where
  constructor monoidLSTMNoise
  field noiseZ noiseR noiseH : Integer
open MonoidLSTMNoise public

record MonoidLSTMControl : Set where
  constructor monoidLSTMControl
  field optimizerToken l2Token : Integer
open MonoidLSTMControl public

record MonoidAffine : Set where
  constructor monoidAffine
  field slope offset : Integer
open MonoidAffine public

_∘ₘ_ : MonoidAffine → MonoidAffine → MonoidAffine
(monoidAffine a₁ b₁) ∘ₘ (monoidAffine a₂ b₂) =
  monoidAffine
    ((_*_) a₁ a₂)
    ((_+_) ((_*_) a₁ b₂) b₁)

monoidAffine-id : MonoidAffine
monoidAffine-id = monoidAffine 1 0

monoidAffine-assoc : ∀ a b c → (a ∘ₘ b) ∘ₘ c ＝ a ∘ₘ (b ∘ₘ c)
monoidAffine-assoc (monoidAffine a₁ b₁) (monoidAffine a₂ b₂) (monoidAffine a₃ b₃) =
  cong₂ monoidAffine
    (mulInteger-assoc a₁ a₂ a₃)
    (trans
      (cong₂ (_+_)
        (mulInteger-assoc a₁ a₂ b₃)
        refl)
      (trans
        (sym (addInteger-assoc
          ((_*_) a₁ ((_*_) a₂ b₃))
          ((_*_) a₁ b₂)
          b₁))
        (cong
          (λ z → (_+_) z b₁)
          (sym (mulInteger-distributeˡ-addInteger
            a₁
            ((_*_) a₂ b₃)
            b₂)))))

monoidAffine-idˡ : ∀ a → monoidAffine-id ∘ₘ a ＝ a
monoidAffine-idˡ (monoidAffine a b) =
  cong₂ monoidAffine
    (mulInteger-idˡ a)
    (trans
      (cong (λ z → (_+_) z 0) (mulInteger-idˡ b))
      (addInteger-idʳ b))

monoidAffine-idʳ : ∀ a → a ∘ₘ monoidAffine-id ＝ a
monoidAffine-idʳ (monoidAffine a b) =
  cong₂ monoidAffine
    (mulInteger-idʳ a)
    (trans
      (cong (λ z → (_+_) z b) (mulInteger-zeroʳ a))
      (addInteger-idˡ b))

applyMonoidAffine : MonoidAffine → Integer → Integer
applyMonoidAffine (monoidAffine a b) c =
  (_+_) ((_*_) a c) b

data MonoidLSTMGate : Set where
  monoidHold monoidWrite monoidReset monoidAccum : MonoidLSTMGate

monoidLSTMGateOf : Integer → MonoidLSTMGate
monoidLSTMGateOf (pos 0) = monoidHold
monoidLSTMGateOf (pos (suc n)) = monoidAccum
monoidLSTMGateOf (negsuc n) = monoidReset

monoidLSTMCellStep : MonoidLSTMGate → Integer → Integer → Integer
monoidLSTMCellStep monoidHold c x = c
monoidLSTMCellStep monoidWrite c x = leaky2 x
monoidLSTMCellStep monoidReset c x = 0
monoidLSTMCellStep monoidAccum c x = (_+_) c (leaky2 x)

monoidLSTMAffineOf : MonoidLSTMGate → Integer → MonoidAffine
monoidLSTMAffineOf monoidHold x = monoidAffine 1 0
monoidLSTMAffineOf monoidWrite x = monoidAffine 0 (leaky2 x)
monoidLSTMAffineOf monoidReset x = monoidAffine 0 0
monoidLSTMAffineOf monoidAccum x = monoidAffine 1 (leaky2 x)

monoidLSTMCellStep-is-affine :
  ∀ g c x →
  monoidLSTMCellStep g c x ＝
  applyMonoidAffine (monoidLSTMAffineOf g x) c
monoidLSTMCellStep-is-affine monoidHold c x =
  trans
    (sym (mulInteger-idˡ c))
    (sym (addInteger-idʳ ((_*_) 1 c)))
monoidLSTMCellStep-is-affine monoidWrite c x =
  trans
    (sym (addInteger-idˡ (leaky2 x)))
    (cong
      (λ z → (_+_) z (leaky2 x))
      (sym (mulInteger-zeroˡ c)))
monoidLSTMCellStep-is-affine monoidReset c x =
  trans
    (sym (addInteger-idˡ 0))
    (cong
      (λ z → (_+_) z 0)
      (sym (mulInteger-zeroˡ c)))
monoidLSTMCellStep-is-affine monoidAccum c x =
  cong (λ z → (_+_) z (leaky2 x)) (sym (mulInteger-idˡ c))

scanMonoidAffine : List Integer → MonoidAffine
scanMonoidAffine [] = monoidAffine-id
scanMonoidAffine (x ∷ xs) =
  scanMonoidAffine xs ∘ₘ monoidLSTMAffineOf (monoidLSTMGateOf x) x

scanMonoidAffine-cons :
  ∀ x xs →
  scanMonoidAffine (x ∷ xs) ＝
  scanMonoidAffine xs ∘ₘ monoidLSTMAffineOf (monoidLSTMGateOf x) x
scanMonoidAffine-cons x xs = refl

runMonoidLSTMCell : List Integer → Integer → Integer
runMonoidLSTMCell xs c₀ =
  applyMonoidAffine (scanMonoidAffine xs) c₀

record MonoidLSTMState : Set where
  constructor monoidLSTMState
  field
    hiddenState : Integer
    cellState : Integer
    matrixState : MonoidLSTMMatrices
    noiseState : MonoidLSTMNoise
    controlState : MonoidLSTMControl
open MonoidLSTMState public

identityMonoidLSTMMatrices : MonoidLSTMMatrices
identityMonoidLSTMMatrices = monoidLSTMMatrices 1 1 1

zeroMonoidLSTMNoise : MonoidLSTMNoise
zeroMonoidLSTMNoise = monoidLSTMNoise 0 0 0

zeroMonoidLSTMControl : MonoidLSTMControl
zeroMonoidLSTMControl = monoidLSTMControl 0 0

monoidLSTMHiddenStep : Integer → Integer → Integer → Integer
monoidLSTMHiddenStep h c x =
  (_+_) c (leaky2 ((_+_) h x))

monoidLSTMStep : MonoidLSTMState → Integer → MonoidLSTMState
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
  ∀ (s : MonoidLSTMState) (x : Integer) →
  persistentMonoidLSTM (monoidLSTMStep s x) ＝
  persistentMonoidLSTM s
persistentMonoidLSTM-preservation
  (monoidLSTMState h c m n g) x = refl

monoidLSTMParameterPersistence :
  ∀ (s : MonoidLSTMState) (x : Integer) →
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
  ∀ (s t : MonoidLSTMState) (x : Integer) →
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

gruMatrices : Integer → Integer → Integer → GRUMatrices
gruMatrices a b c = monoidLSTMMatrices a b c

gruNoise : Integer → Integer → Integer → GRUNoise
gruNoise a b c = monoidLSTMNoise a b c

mkGlobalControl : Integer → Integer → GlobalControl
mkGlobalControl a b = monoidLSTMControl a b

gruState :
  Integer →
  Integer →
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

rationalCodeCode : RationalCode → Integer
rationalCodeCode q = fromNat (rationalCodeNumeratorMagnitude q)

identityActivation8 : Integer → Integer
identityActivation8 x = x

identityActivation8-law : ∀ x → identityActivation8 x ＝ x
identityActivation8-law x = refl

identityActivation8-zero : identityActivation8 0 ＝ 0
identityActivation8-zero = refl

gruCandidate8 : Integer → Integer → Integer
gruCandidate8 h x = (_+_) h x

complement128 : Integer → Integer
complement128 g = (_-_) 1 g

mix8 : Integer → Integer → Integer → Integer
mix8 g old new =
  (_+_)
    ((_*_) (complement128 g) old)
    ((_*_) g new)

gateCode : Signed → Integer
gateCode (signedNeg n) = 0
gateCode signedZer = 0
gateCode (signedPos n) = 1

gateFromInput : Integer → Integer
gateFromInput x = gateCode (signedCode x)

monoidLSTMRecurrentStep : MonoidLSTMState → Integer → MonoidLSTMState
monoidLSTMRecurrentStep = monoidLSTMStep

gruStep : GRUState → Integer → GRUState
gruStep = monoidLSTMStep

persistentGRU :
  GRUState →
  GRUMatrices × (GRUNoise × GlobalControl)
persistentGRU = persistentMonoidLSTM

persistent-preservation :
  ∀ (s : GRUState) (x : Integer) →
  persistentGRU (gruStep s x) ＝ persistentGRU s
persistent-preservation s x =
  persistentMonoidLSTM-preservation s x

gruParameterPersistence :
  ∀ (s : GRUState) (x : Integer) →
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
  ∀ (s t : GRUState) (x : Integer) →
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

inputGRUAction : Integer → GRUAction
inputGRUAction x = gruAction (λ s → monoidLSTMStep s x)

record RecurrentNetwork (State Input : Set) : Set₁ where
  constructor recurrentNetwork
  field
    runNetwork : State → Input → State
open RecurrentNetwork public

canonicalMonoidLSTMRecurrentNetwork :
  RecurrentNetwork MonoidLSTMState Integer
canonicalMonoidLSTMRecurrentNetwork =
  recurrentNetwork monoidLSTMStep

canonicalMonoidLSTMNetwork-law :
  ∀ (s : MonoidLSTMState) (x : Integer) →
  runNetwork canonicalMonoidLSTMRecurrentNetwork s x ＝
  monoidLSTMStep s x
canonicalMonoidLSTMNetwork-law s x = refl

canonicalGRURecurrentNetwork : RecurrentNetwork GRUState Integer
canonicalGRURecurrentNetwork =
  recurrentNetwork gruStep

canonicalGRUNetwork-law :
  ∀ (s : GRUState) (x : Integer) →
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
recurrentPrefixState R xs (suc n) s =
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
recurrentPrefixEndomorphism R xs (suc n) =
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
recurrentPrefix-correct R xs (suc n) s =
  cong
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
  cong
    (λ k → recurrentPrefixState R xs k s)
    (plus-zero m)
recurrentPrefix-split R xs m (suc n) s =
  trans
    (cong
      (λ k → recurrentPrefixState R xs k s)
      (plus-succ m n))
    (cong
      (λ z → runNetwork R z (xs (m + n)))
      (recurrentPrefix-split R xs m n s))

canonicalMonoidLSTM-recurrent-prefix-correct :
  ∀ (xs : ℕ → Integer) (n : ℕ) (s : MonoidLSTMState) →
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
  ∀ (xs : ℕ → Integer) (m n : ℕ) (s : MonoidLSTMState) →
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
  ∀ (xs : ℕ → Integer) (n : ℕ) (s : GRUState) →
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
  ∀ (xs : ℕ → Integer) (m n : ℕ) (s : GRUState) →
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
  field thetaQ rTheta eQ rE rL : Integer
open F4IntUState public

record F4IntUKernel : Set₁ where
  constructor f4IntUKernel
  field globalL2 : Integer
open F4IntUKernel public

f4ThetaFull : F4IntUState → Integer
f4ThetaFull s = thetaQ s

f4ThetaFull-law : ∀ s → f4ThetaFull s ＝ thetaQ s
f4ThetaFull-law s = refl

l2Correction : Integer → Integer
l2Correction x = lcbNegate x

f4ThetaStep : F4IntUKernel → F4IntUState → Integer → F4IntUState
f4ThetaStep K s g =
  f4IntUState
    ((_+_) ((_+_) (thetaQ s) g) (l2Correction (globalL2 K)))
    0 (eQ s) (rE s) (rL s)

f4ParameterInvariant : ∀ (K : F4IntUKernel) (s : F4IntUState) (g : Integer) →
  thetaQ (f4ThetaStep K s g) ＝
  (_+_) ((_+_) (thetaQ s) g) (l2Correction (globalL2 K))
f4ParameterInvariant K s g = refl

HaarAccumulator : Set
HaarAccumulator = Integer × Integer


------------------------------------------------------------------------
-- Haar-featured linear transformer.
--
-- Haar mixing remains exact integer arithmetic, now used as a feature map
-- inside a parameterized linear-attention accumulator.  The accumulator
-- is additive and therefore itself forms a monoid; sequence processing is
-- a pure left-to-right scan over rank-one feature updates.
------------------------------------------------------------------------

CanonicalHaarPair : Set
CanonicalHaarPair = Integer × Integer

canonicalHaarMix : Integer → Integer → CanonicalHaarPair
canonicalHaarMix x y =
  (_+_) x y , (_-_) x y

canonicalHaarMix-left : ∀ x y →
  fst (canonicalHaarMix x y) ＝ (_+_) x y
canonicalHaarMix-left x y = refl

canonicalHaarMix-right : ∀ x y →
  snd (canonicalHaarMix x y) ＝ (_-_) x y
canonicalHaarMix-right x y = refl

canonicalHaarMix-linear-form :
  ∀ x y →
  canonicalHaarMix x y ＝
  ((_+_) x y , (_-_) x y)
canonicalHaarMix-linear-form x y = refl

canonicalReLU8 : Integer → Integer
canonicalReLU8 x with hardSign x
... | negativeSign = 0
... | zeroSign = 0
... | positiveSign = x

canonicalCReLU8 : Integer → CanonicalHaarPair
canonicalCReLU8 x =
  canonicalReLU8 x , canonicalReLU8 (negateInteger x)

------------------------------------------------------------------------
-- Fraction-code CReLU': CReLU with a numerator/denominator softsign map on
-- the negative branch. This is executable rational-code arithmetic, not a
-- normalized quotient-type rational or a proof of rational-code equivalence.
------------------------------------------------------------------------

canonicalSignReLU' : RationalCode → RationalCode
canonicalSignReLU' (negsuc n , denominatorMinusOne) =
  negsuc n , denominatorMinusOne + suc n
canonicalSignReLU' q = q

rationalCodeNegate : RationalCode → RationalCode
rationalCodeNegate (numerator , denominatorMinusOne) =
  negateInteger numerator , denominatorMinusOne

CanonicalCReLUPrimePair : Set
CanonicalCReLUPrimePair = RationalCode × RationalCode

canonicalCReLU' : RationalCode → CanonicalCReLUPrimePair
canonicalCReLU' x =
  canonicalSignReLU' x , canonicalSignReLU' (rationalCodeNegate x)


canonicalHaarFeature : Integer → CanonicalHaarPair
canonicalHaarFeature x =
  canonicalHaarMix
    (fst (canonicalCReLU8 x))
    (snd (canonicalCReLU8 x))

canonicalHaarFeature-left : ∀ x →
  fst (canonicalHaarFeature x) ＝
  (_+_)
    (fst (canonicalCReLU8 x))
    (snd (canonicalCReLU8 x))
canonicalHaarFeature-left x = refl

canonicalHaarFeature-right : ∀ x →
  snd (canonicalHaarFeature x) ＝
  (_-_)
    (fst (canonicalCReLU8 x))
    (snd (canonicalCReLU8 x))
canonicalHaarFeature-right x = refl

canonicalHaarOrthogonalCross :
  (_+_)
    ((_*_) 1 1)
    ((_*_) 1 (negateInteger 1))
  ＝ 0
canonicalHaarOrthogonalCross = refl

canonicalHaarFeatureReconstruct :
  ∀ x →
  let p = fst (canonicalCReLU8 x)
      n = snd (canonicalCReLU8 x)
  in (_-_) p n ＝ x
canonicalHaarFeatureReconstruct
  (pos 0) = refl
canonicalHaarFeatureReconstruct
  (pos (suc n)) = refl
canonicalHaarFeatureReconstruct
  (negsuc n) = addInteger-idˡ (negsuc n)

canonicalHaarFeatureInjective :
  ∀ {x y} →
  canonicalCReLU8 x ＝ canonicalCReLU8 y →
  x ＝ y
canonicalHaarFeatureInjective {x} {y} eq =
  trans
    (sym (canonicalHaarFeatureReconstruct x))
    (trans
      (cong₂
        (λ a b → (_-_) a b)
        (cong fst eq)
        (cong snd eq))
      (canonicalHaarFeatureReconstruct y))

record HaarFeaturedLinearTransformer : Set where
  constructor haarFeaturedLinearTransformer
  field
    qProjection kProjection vProjection : Integer → Integer
open HaarFeaturedLinearTransformer public

haarAccumulator-id : HaarAccumulator
haarAccumulator-id = 0 , 0

haarAccumulator-op :
  HaarAccumulator → HaarAccumulator → HaarAccumulator
haarAccumulator-op (a₁ , b₁) (a₂ , b₂) =
  (_+_) a₁ a₂ , (_+_) b₁ b₂

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
    (addInteger-assoc a₁ a₂ a₃)
    (addInteger-assoc b₁ b₂ b₃)

haarAccumulator-op-idˡ :
  ∀ x →
  haarAccumulator-op haarAccumulator-id x ＝ x
haarAccumulator-op-idˡ (a , b) =
  cong₂ _,_
    (addInteger-idˡ a)
    (addInteger-idˡ b)

haarAccumulator-op-idʳ :
  ∀ x →
  haarAccumulator-op x haarAccumulator-id ＝ x
haarAccumulator-op-idʳ (a , b) =
  cong₂ _,_
    (addInteger-idʳ a)
    (addInteger-idʳ b)

haarKeyValueContribution :
  HaarFeaturedLinearTransformer →
  Integer →
  HaarAccumulator
haarKeyValueContribution T x =
  let (kp , kn) =
        canonicalHaarFeature
          (kProjection T x)
      v = vProjection T x
  in (_*_) kp v , (_*_) kn v

haarAccumulatorStep :
  HaarFeaturedLinearTransformer →
  HaarAccumulator →
  Integer →
  HaarAccumulator
haarAccumulatorStep T s x =
  haarAccumulator-op s
    (haarKeyValueContribution T x)

haarQueryRead :
  HaarFeaturedLinearTransformer →
  HaarAccumulator →
  Integer →
  Integer
haarQueryRead T (sp , sn) x =
  let (qp , qn) =
        canonicalHaarFeature
          (qProjection T x)
  in (_+_)
       ((_*_) qp sp)
       ((_*_) qn sn)

haarLinearTransform :
  HaarFeaturedLinearTransformer →
  HaarAccumulator →
  List Integer →
  List Integer
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
  List Integer →
  List Integer
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
    qLogValue : RationalCode
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
CanonicalFullLearnerState = FullLearnerState ⊤

CanonicalFullLearnerKernel : Set₁
CanonicalFullLearnerKernel = FullLearnerKernel ⊤

canonicalPolicy : ∀ {A : Set} → FullLearnerKernel A → FullLearnerState A → ℕ
canonicalPolicy K s = sparsemaxPolicy (actionSpaceK K) (lcbScore (lcbKernel K) (lcbCounts s) (critic (watkins s))) (valuesCount (lcbCounts s))

canonicalPolicyWeight : ∀ {A : Set} → FullLearnerKernel A → FullLearnerState A → SparseWeight
canonicalPolicyWeight K s = sparsemaxWeight (actionSpaceK K) (lcbScore (lcbKernel K) (lcbCounts s) (critic (watkins s))) (valuesCount (lcbCounts s)) (canonicalPolicy K s)

canonicalPolicyWeightCode : ∀ {A : Set} → FullLearnerKernel A → FullLearnerState A → Integer

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

canonicalPolicyWeightCode K s = fromNat (numerator (canonicalPolicyWeight K s))

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
    z≤n

softSparse-zero-to-hardSparse :
  ∀ {A}
  (K : FullLearnerKernel A)
  (s : FullLearnerState A) →
  SoftSparseBounded K s zero →
  HardSparse K s
softSparse-zero-to-hardSparse K s h {a} distinct =
  sym (≤-antisym z≤n (h distinct))

replaceOptimizer : ∀ {A} → FullLearnerState A → F4IntUState → FullLearnerState A
replaceOptimizer s o = fullLearnerState (watkins s) (gru s) o
  (lcbCounts s) (qLogControl s) (qLogValue s) (haarAccumulator s)

canonicalPolicy-optimizer-invariant :
  ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) (o : F4IntUState) →
  canonicalPolicy K (replaceOptimizer s o) ＝ canonicalPolicy K s
canonicalPolicy-optimizer-invariant K s o = refl

maxCriticValueList : List Integer → Integer
maxCriticValueList [] = 0
maxCriticValueList (x ∷ xs) with compareInt8 x (maxCriticValueList xs)
... | less = maxCriticValueList xs
... | equal = maxCriticValueList xs
... | greater = x

maxCriticValue8 : ∀ {A : Set} → ActionSpace A → CriticState A → Integer
maxCriticValue8 K q = maxCriticValueList (map (λ a → values q a) (candidates K))

canonicalQLogBias : ∀ {A} → FullLearnerKernel A → FullLearnerState A → Integer
canonicalQLogBias K s = qLog2Bias8 (canonicalPolicyWeightCode K s)

canonicalReward8 : ∀ {A} → FullLearnerKernel A → FullLearnerState A → Integer
canonicalReward8 K s = canonicalPolicyWeightCode K s

canonicalDiscount8 : Integer
canonicalDiscount8 = 1

canonicalGRUFeedback : ∀ {A} → FullLearnerState A → Integer
canonicalGRUFeedback s = hiddenState (gru s)

canonicalF4L2Feedback : ∀ {A} → FullLearnerKernel A → FullLearnerState A → Integer
canonicalF4L2Feedback K s =
  (_+_)
    (f4ThetaFull (optimizer s))
    (l2Correction (globalL2 (optimizerKernel K)))

canonicalQLogControlFeedback : ∀ {A} → FullLearnerState A → Integer
canonicalQLogControlFeedback s = coefficient (qLogControl s)

canonicalQLogValueFeedback : ∀ {A} → FullLearnerState A → Integer
canonicalQLogValueFeedback s = rationalCodeCode (qLogValue s)

canonicalEndogenousFeedback : ∀ {A} → FullLearnerKernel A → FullLearnerState A → Integer
canonicalEndogenousFeedback K s =
  (_+_)
    (canonicalGRUFeedback s)
    ((_+_)
        (canonicalF4L2Feedback K s)
        ((_+_)
          (canonicalQLogControlFeedback s)
          (canonicalQLogValueFeedback s)))

canonicalWatkinsTarget : ∀ {A} → FullLearnerKernel A → FullLearnerState A → Integer
canonicalWatkinsTarget K s =
  (_+_)
    ((_+_)
      ((_+_) (canonicalReward8 K s) (canonicalQLogBias K s))
      ((_*_) canonicalDiscount8 (maxCriticValue8 (actionSpaceK K) (critic (watkins s)))))
    (canonicalEndogenousFeedback K s)

canonicalWatkinsTarget-law : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) →
  canonicalWatkinsTarget K s ＝
  (_+_)
    ((_+_)
      ((_+_) (canonicalReward8 K s) (canonicalQLogBias K s))
      ((_*_) canonicalDiscount8 (maxCriticValue8 (actionSpaceK K) (critic (watkins s)))))
    (canonicalEndogenousFeedback K s)
canonicalWatkinsTarget-law K s = refl

canonicalQLogControlStep : ∀ {A} → FullLearnerKernel A → FullLearnerState A → SignedQLogControl
canonicalQLogControlStep K s =
  signedQLogControl negativeAlpha8 (canonicalQLogBias K s)

canonicalSignal : ∀ {A} → FullLearnerKernel A → FullLearnerState A → Integer
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
  Integer
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

canonicalQLogStep : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) → RationalCode
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
  -- The compiler-owned sized-type builtins are already registered by
  -- the selected Agda profile. Do not bind them a second time here:
  -- reissuing BUILTIN SIZEUNIV after Agda.Builtin.Size is loaded fails with
  -- DuplicateBuiltinBinding. The nested module consumes the existing names.
  -- Agda2HS compiles recursive streams through this erased-size lazy tail.
  open import Haskell.Prim.Thunk using (Thunk; force; Size; Size<_; ∞)
  
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
learnerStreamAt (suc n) trace =
  learnerStreamAt n (learnerStreamTail trace)


iterateCanonical : ∀ {A} → FullLearnerKernel A → ℕ → FullLearnerState A → FullLearnerState A
iterateCanonical K zero s = s
iterateCanonical K (suc n) s = canonicalFullStep K (iterateCanonical K n s)

iterateCanonical-step-shift :
  ∀ {A}
  (K : FullLearnerKernel A)
  (n : ℕ)
  (s : FullLearnerState A) →
  iterateCanonical K n (canonicalFullStep K s) ＝
  iterateCanonical K (suc n) s
iterateCanonical-step-shift K zero s = refl
iterateCanonical-step-shift K (suc n) s =
  cong (canonicalFullStep K) (iterateCanonical-step-shift K n s)

canonicalLearnerTraceAt :
  ∀ {A}
  (K : FullLearnerKernel A)
  (s : FullLearnerState A)
  (n : ℕ) →
  learnerStreamAt n (canonicalLearnerTrace K s) ＝
  iterateCanonical K n s
canonicalLearnerTraceAt K s zero = refl
canonicalLearnerTraceAt K s (suc n) =
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

canonicalTotalCountStep : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) → totalCount (lcbCounts (canonicalFullStep K s)) ＝ suc (totalCount (lcbCounts s))
canonicalTotalCountStep K s = refl

canonicalNoFixedPoint :
  ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) →
  canonicalFullStep K s ≠ s
canonicalNoFixedPoint K s eq =
  plus-succ-not-self (totalCount (lcbCounts s)) zero
    (trans (plus-succ (totalCount (lcbCounts s)) zero)
      (trans (cong suc (plus-zero (totalCount (lcbCounts s))))
        (trans (sym (canonicalTotalCountStep K s))
          (cong (λ t → totalCount (lcbCounts t)) eq))))


canonicalTotalCountAfter :
  ∀ {A} (K : FullLearnerKernel A) (n : ℕ) (s : FullLearnerState A) →
  totalCount (lcbCounts (iterateCanonical K n s)) ＝
  totalCount (lcbCounts s) + n
canonicalTotalCountAfter K zero s = sym (plus-zero (totalCount (lcbCounts s)))
canonicalTotalCountAfter K (suc n) s =
  trans
    (canonicalTotalCountStep K (iterateCanonical K n s))
    (trans
      (cong suc (canonicalTotalCountAfter K n s))
      (sym (plus-succ (totalCount (lcbCounts s)) n)))

canonicalAperiodic : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) (n : ℕ) → iterateCanonical K (suc n) s ≠ s
canonicalAperiodic K s n cyc = plus-succ-not-self (totalCount (lcbCounts s)) n
  (trans
    (sym (canonicalTotalCountAfter K (suc n) s))
    (cong (λ t → totalCount (lcbCounts t)) cyc))

canonicalOrbitNonFixed : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) (n : ℕ) → iterateCanonical K n s ≠ canonicalFullStep K (iterateCanonical K n s)
canonicalOrbitNonFixed K s n eq =
  canonicalNoFixedPoint K (iterateCanonical K n s) (sym eq)

canonicalNoNontrivialFiniteCycle : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) (n : ℕ) → iterateCanonical K (suc n) s ＝ s → ⊥
canonicalNoNontrivialFiniteCycle K s n cyc = canonicalAperiodic K s n cyc

canonicalTotalCountIterate2 : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) → totalCount (lcbCounts (iterateCanonical K 2 s)) ＝ suc (suc (totalCount (lcbCounts s)))
canonicalTotalCountIterate2 K s = refl

canonicalNoCountedTwoCycle : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) → iterateCanonical K 2 s ＝ s → ⊥
canonicalNoCountedTwoCycle K s cyc = succ-succ-not-self (totalCount (lcbCounts s))
  (trans (sym (canonicalTotalCountIterate2 K s))
    (cong (λ t → totalCount (lcbCounts t)) cyc))

temperatureCodeLaw : sparsemaxTemperature ＝ 16
temperatureCodeLaw = refl

pessimisticInit : Integer
pessimisticInit = fromNat 128

pessimisticCritic : ∀ {A} → CriticState A
pessimisticCritic {A} = criticState (λ _ → pessimisticInit)

pessimisticCritic-law : ∀ {A} (i : ℕ) → values (pessimisticCritic {A = A}) i ＝ pessimisticInit
pessimisticCritic-law {A = A} i = refl

canonicalPersistent : ∀ {A} (K : FullLearnerKernel A) (s : FullLearnerState A) → persistentGRU (canonicalGRUStep K s) ＝ persistentGRU (gru s)
canonicalPersistent = canonicalPersistentGRUPreservation

CanonicalToken : Set
CanonicalToken = Integer

CanonicalTokenSequence : Set
CanonicalTokenSequence = List CanonicalToken

canonicalTokenEncode : CanonicalToken → Integer
canonicalTokenEncode = λ token → token

-- Tokens use the official Agda2HS Prelude Integer carrier directly. The identity
-- encoding/decoding gives a total left inverse and global injectivity.
canonicalTokenEncodeLeftInverse :
  ∀ token → canonicalTokenEncode token ＝ token
canonicalTokenEncodeLeftInverse token = refl

canonicalTokenEncodeInjective :
  ∀ {left right} →
  canonicalTokenEncode left ＝ canonicalTokenEncode right →
  left ＝ right
canonicalTokenEncodeInjective {left} {right} encodedEquality =
  trans
    (sym (canonicalTokenEncodeLeftInverse left))
    (trans
      (cong (λ x → x) encodedEquality)
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
      (cong inverse observationEquality)
      (leftInverse right))

canonicalTokenEncodeList : CanonicalTokenSequence → List Integer
canonicalTokenEncodeList = map canonicalTokenEncode

canonicalTokenEncodeListLeftInverse :
  ∀ tokens → map (λ x → x) (canonicalTokenEncodeList tokens) ＝ tokens
canonicalTokenEncodeListLeftInverse [] = refl
canonicalTokenEncodeListLeftInverse (token ∷ tokens) =
  cong (_∷_ token) (canonicalTokenEncodeListLeftInverse tokens)

canonicalTokenEncodeListInjective :
  ∀ {left right} →
  canonicalTokenEncodeList left ＝ canonicalTokenEncodeList right →
  left ＝ right
canonicalTokenEncodeListInjective {left} {right} encodedEquality =
  trans
    (sym (canonicalTokenEncodeListLeftInverse left))
    (trans
      (cong (map (λ x → x)) encodedEquality)
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
CanonicalTokenLogitVector = CanonicalToken → Integer

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


