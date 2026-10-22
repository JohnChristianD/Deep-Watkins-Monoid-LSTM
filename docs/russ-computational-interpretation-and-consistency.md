# RUSS computation, metatheory, and repository refactor

## Scope and current claim

The maintained Agda source consists of exactly two non-site monoliths:
FullCoupled/CanonicalLearnerMonolith.agda and FullCoupled/TheoremsMonolith.agda.
The theorem monolith no longer contains the repository's A*/e-graph framework. The retired
graph-search wrappers, generated JavaScript extractor, presentation Agda module, and related CI
lanes are removed. Static Pages are rendered by Fennel at build time; published output is
HTML and CSS without browser JavaScript.

**Global RUSS consistency is not certified.** The static Pages contract checks this statement.

## Computational interpretation

The canonical learner's RussianRecursiveMathematicsBasis has one explicit trust entry:
russianRecursiveMathematicsAssumptions. The basis packages three assumptions without
classical excluded-middle principles.

* **Markov principle.** russSearchBounded is structural recursion on finite fuel. It checks a
  finite prefix in deterministic order. A found result carries a SigmaWitness; exhaustion means
  only that no witness occurred in the checked prefix. It does not establish unbounded
  termination by ordinary reduction. russianMarkovPrinciple remains an assumption.
* **ECT0.** extendedChurchThesis0 exposes the register-machine program witness from the basis.
  runMachineFuel and runMachineWithFuel provide finite operational evaluation, with halted traces
  distinct from fuel exhaustion. A program for each eligible relation still comes from the ECT0
  field, not evaluating arbitrary relation data.
* **Countable choice.** constructiveCountableChoice computes a selector when each index
  already supplies data-level SigmaWitness evidence. The Prop-valued russianCountableChoice
  projection does not extract erased proof evidence into a runtime selector.

The natural-deduction calculus in RUSSProofTheory has a formula language, derivation constructors,
an interpretation in the supplied basis, and a structural soundness theorem. russCoreConsistency
proves that the small object calculus cannot derive its false formula, conditional on an inhabitant
of that basis. russCurrentBasisRelativeConsistency instantiates the claim using the repository's
postulated basis. This is not an independent model of the basis and does not certify consistency
of the combined theory.

## Metatheoretic obligation

An independent consistency certification needs a model or relative-consistency proof for this
exact combined dependent theory and transitive dependencies. It must cover the Markov encoding;
ECT0's register-machine relation and the arithmetic bridge to computation traces; Prop-valued
countable choice; imported theories; Reflection/TC primitive signatures and compiler ABI;
substitution, conversion, rewrite-rule subject reduction and confluence; and the trusted Agda
checker/compiler boundary. A successful kernel check establishes well-typedness relative to those
assumptions; it is not a model of their joint consistency.

Pédrot's results motivate, but do not discharge, this obligation. The 2020 paper Russian
Constructivism in a Prefascist Theory models Markov's principle for a particular CIC setting.
The 2024 paper Upon This Quote I Will Build My Church Thesis studies quotation-based
Church-thesis principles in a separate MLTT setting. Neither result directly establishes
consistency of this repository's precise MP + ECT0 + Prop-choice signature or its complete
imported/primitive closure. Cockx, Tabareau, and Winterhalter explain why rewrite confluence and
subject reduction deserve explicit treatment. No classical logic is inferred.

## Agda2HS types and rational-code boundary

The public Agda2HS Prelude lists Integer but explicitly lists Rational as missing. PreludeInt is
not an appropriate replacement for the established Integer name. Local integer operator aliases
refer to imported arithmetic; no duplicate integer carrier is introduced. Genuine name clashes
should be resolved through public names and narrow import hiding, not a second numeric type.
The canonical sources use Haskell.Prelude and do not import non-reflection Agda.Builtin modules.

RationalCode is an executable encoding in the shared Agda2HS-compatible fragment: signed
Integer numerator and natural denominator-minus-one. Its denominator is suc d, so zero
denominator is not representable. rationalCodeCrossProductEqual states a cross-product comparison
condition; rationalCodeRepresentationEqual is strict code equality. The encoding is not
gcd-normalized and is not a quotient type. The cross-product condition has not yet been proved
equivalent to equality in a chosen quotient construction. A legacy magnitude helper maps negative
numerators to zero for the existing approximation; this is not general rational arithmetic.
A proper rational field needs proved arithmetic and equivalence laws before it can be called a
full implementation of the rationals. Exact reals require a constructive completion and convergence
laws; no real-number implementation is claimed.

## Search verdict

The old A*/e-graph subsystem was a dependency/capability planner and supplied-rewrite equality
framework, not a theorem-discovery kernel. A heuristic can rank plans inside an encoded graph;
it cannot synthesize and certify a new proof by itself. A real discovery pipeline needs conjecture
generation, proof-term synthesis, exact Agda checking, and provenance containing source hashes,
assumptions, imports, options, and minimized dependencies. This branch removes the search
subsystem rather than presenting its former planning behavior as theorem discovery.

## References

* nLab, Russian constructivism: https://ncatlab.org/nlab/show/Russian%2Bconstructivism
* Stanford Encyclopedia of Philosophy, Constructive Mathematics:
  https://plato.stanford.edu/entries/mathematics-constructive/
* Pédrot, Russian Constructivism in a Prefascist Theory (LICS 2020):
  https://doi.org/10.1145/3373718.3394740
* Pédrot, Upon This Quote I Will Build My Church Thesis (LICS 2024):
  https://doi.org/10.1145/3661814.3662070
* Cockx, Tabareau, Winterhalter, The Taming of the Rew (POPL 2021):
  https://doi.org/10.1145/3434341
* Agda documentation, rewriting and confluence:
  https://agda.readthedocs.io/en/latest/language/rewriting.html
* Agda2HS public library API: https://agda.github.io/agda2hs/lib/
* Agda2HS feature documentation: https://agda.github.io/agda2hs/features.html
* Haskell Wikibooks, denotational semantics:
  https://en.wikibooks.org/wiki/Haskell/Denotational_semantics
* Haskell Wikibooks, Typeclassopedia:
  https://en.wikibooks.org/wiki/Haskell/Typeclassopedia
* EuroForth proceedings index: https://euroforth.org/
* Girard, Linear Logic: https://doi.org/10.1145/143165.143187

