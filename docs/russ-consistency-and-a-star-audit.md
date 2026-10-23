RUSS operational interpretation and trust-boundary audit
=======================================================

Scope
-----

This audit applies to the two canonical Agda monoliths: FullCoupled/CanonicalLearnerMonolith.agda and FullCoupled/TheoremsMonolith.agda. It deliberately does not claim that a source inventory, generated Pages index, or successful type-check is an unconditional consistency certificate for the entire repository.

Computational interpretation
-----------------------------

The record RussianRecursiveMathematicsBasis groups the selected RUSS assumptions into three projections: decidable Markov search, register-machine Extended Church's Thesis 0 (ECT₀), and proposition-valued countable choice. The name russianRecursiveMathematicsAssumptions is the one opaque basis postulate. Its projections are not rewrite rules, and the computational code does not silently replace those assumptions with classical logic.

Markov principle. The functions russSearchBounded and russMarkovOperationalPrefix perform a structurally recursive, finite search over a decidable predicate. A result contains either a witness with evidence or an explicit fuel-exhausted constructor. Fuel exhaustion says only that the inspected prefix contained no witness; it neither proves non-existence nor establishes termination of unbounded search. Deriving an unbounded witness from double-negated existence still uses the declared Markov field.

ECT₀. The machine interface represents registers, instructions, configurations, finite steps, traces, halting and output. runMachineFuel is bounded by an explicit natural-number fuel value. russECT0CertifiedProgram obtains a program by projecting the ECT₀ field from the supplied basis and packages it with ComputesRelation evidence. That projection is an assumption application, not a reduction compiling arbitrary relation data. A complete model still needs a proved arithmetic representation bridge from machine traces to the exact object-language computation predicate.

Countable choice. russPropCountableSelector exposes the proposition-valued interface. It does not extract erased proposition evidence into a runtime function. russDataCountableSelector instead works from supplied data-level SigmaWitness values. These interfaces are intentionally distinct.

Pédrot and dependent syntax
----------------------------

The repository includes a proof-level axiom-tag calculus and a staged operational interface, not a complete Pédrot model of dependent MLTT. The context/type translation, substitution action, dependent elimination, conversion preservation, and semantic preservation theorem have not been implemented as a complete syntactic presheaf model. Pédrot's 2020 MP model and 2024 quotation-based Church-thesis development are design references; their published consistency results do not automatically transfer to this repository's theory.

Separate metatheoretic result
-----------------------------

Within RUSSProofTheory, russSoundness is induction over the explicit RUSSDerivation constructors. Context membership is interpreted by an environment; implication introduction extends the environment; implication elimination applies the interpreted implication; each RUSS axiom tag is interpreted by its matching field in the basis. Falsehood denotes EmptyComputability, which has no constructors. Therefore russCoreConsistency proves that no derivation of falsehood exists in the empty context, for every supplied RussianRecursiveMathematicsBasis.

russCurrentBasisRelativeConsistency instantiates this theorem with russianRecursiveMathematicsAssumptions. The precise result is relative consistency of the small propositional object calculus, conditional on the named basis. It is not a proof of consistency for the entire Agda import closure, the Agda language, the compiler, or the trusted checker.

A genuine whole-repository metatheorem would need a model or relative-consistency proof for the exact combination of MLTT rules and imports. Obligations include the actual Markov principle encoding, ECT₀'s machine semantics and representation theorem, proposition-valued choice, imported Agda2HS definitions, Reflection and type-checking primitives, rewriting and conversion, confluence, subject reduction, mutual recursion, sized types and coinduction, and the checker/compiler trust boundary. No classical excluded-middle axiom is introduced as a RUSS principle. Whole-repository consistency remains unproved.

Rewrite and sized/coinductive rules
-----------------------------------

The OPTIONS pragmas on both canonical monoliths are intentionally unchanged in this branch, including --with-K and --no-guardedness. This preserves the current non-cubical proof configuration; it does not certify rewrite-system metatheory. Confluence checking is a useful Agda check, but an overall consistency proof would still have to establish the relevant metatheory of every enabled rule and imported primitive, not infer it from one pragma.

A-star/e-graph verdict
----------------------

The old search subsystem planned over supplied capability/dependency records and saturated supplied expressions with supplied rewrite rules. It did not generate conjectures, synthesize new Agda proof terms, or independently kernel-check newly discovered theorem statements. Its regressions tested bookkeeping such as dependency order, branching, cycle rejection and priority tie-breaking. Its empty-type Boolean probe was not a consistency proof. The A-star/e-graph applications, standalone graph-search modules, scheduled semantic-registry workflow, and stale callers are removed in this branch.

A true theorem-discovery pipeline would require conjecture generation, proof-term synthesis, exact-head Agda checking, and provenance records that retain statement hashes, assumptions, imported axioms, source dependencies, and minimized proof dependencies. Search can prioritize candidates; only the trusted type checker determines whether a submitted proof term type-checks relative to its theory.

Agda2HS integer, rational and real arithmetic
---------------------------------------------

The canonical module imports Integer from the official Haskell.Prelude export. The removed PreludeInt workaround was not warranted. IntCode is a project-level wrapper that packages values of the imported Integer for the existing integer-law and representation layer; it is not a second implementation of the Integer type. It should only be deleted after its theorem consumers have been moved directly onto the Agda2HS Integer interface and type-checking confirms that the wrapper was redundant.

The public Agda2HS Prelude documentation lists Rational as missing; it does not offer a verified built-in Real implementation. Agda2HS does support user-defined rewrite-rule configuration and custom Haskell imports. Accordingly, the correct rational route is to define and prove an Agda-side exact rational representation and its laws, then map its extraction-compatible computational representation to Haskell Rational through Agda2HS rewrite rules and an explicit Data.Ratio import. The rewrite mapping affects extraction and is not itself proof of canonical equality, arithmetic laws, ordering or normalization.

For constructive reals, an arbitrary fraction or dyadic code is not by itself a complete real field. A Cauchy-pair or signed-digit representation needs an explicit convergence/equality relation and proofs for arithmetic, order and any completeness property claimed. The 2024 Exact Real Search thesis formalises signed-digit encodings, searchable types, optimization and regression in a constructive Agda development. Its techniques can guide a later exact-real implementation, but its library cannot simply be imported into this Agda2HS-only import closure without checking compatibility, options, and theorems. No unsound real field or unsupported builtin is added by this pruning change.

Immutable program surface
-------------------------

site/render.mjs is a pure string-to-string transformation over a frozen catalog, frozen page model, and template. Its filesystem/process effects are isolated in site/app.mjs. The generated output is static HTML and CSS with no browser JavaScript. The Fennel catalog and palette computations use recursive persistent lists and functional transformations; file reads/writes remain at the command-line boundary. FunctionalScript documents a stricter pure-JavaScript subset, but it is not treated as a verified compiler or as the proof kernel for this repository.

References (excluding Cambridge, IO domains, Wikipedia and web archives)
------------------------------------------------------------------------

nLab, Russian constructivism: https://ncatlab.org/nlab/show/Russian%2Bconstructivism

Stanford Encyclopedia of Philosophy, Constructive Mathematics: https://plato.stanford.edu/entries/mathematics-constructive/

Pierre-Marie Pédrot, Russian Constructivism in a Prefascist Theory, LICS 2020, DOI 10.1145/3373718.3394740: https://doi.org/10.1145/3373718.3394740

Pierre-Marie Pédrot, Upon This Quote I Will Build My Church Thesis, LICS 2024, DOI 10.1145/3661814.3662070: https://doi.org/10.1145/3661814.3662070

Cockx, Tabareau and Winterhalter, The Taming of the Rew, POPL 2021, DOI 10.1145/3434341: https://doi.org/10.1145/3434341

Official Agda2HS library surface: https://agda.github.io/agda2hs/lib/

Official Agda2HS rewrite rules and Prelude import documentation: https://agda.github.io/agda2hs/features.html

Todd Waugh Ambridge, Exact Real Search: Formalised Optimisation and Regression in Constructive Univalent Mathematics, PhD thesis, 2024: https://etheses.bham.ac.uk/id/eprint/14662

TypeTopology's thesis index and associated Agda formalisation: https://martinescardo.github.io/TypeTopology/TWA.Thesis.index.html

XDS-Agda, machine-checked Scott-Strachey denotational semantics: https://pdmosses.github.io/xds-agda/

Haskell Wikibooks, Denotational semantics: https://en.wikibooks.org/wiki/Haskell/Denotational_semantics

FunctionalScript repository: https://github.com/functionalscript/functionalscript

Verification statement
----------------------

This branch is a source-and-CI refactor. Its proposed PR must be checked by exact-head CI before any build claim is made. Even if every lane succeeds, the supported conclusion remains: both monoliths pass Agda checking relative to their imports and postulates; RUSSProofTheory proves only its relative object-calculus result; full repository consistency is not certified.