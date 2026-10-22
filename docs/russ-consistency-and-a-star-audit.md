RUSS computation, metatheory, and theorem-search audit

Audit baseline: Deep-Watkins-Monoid-LSTM, main revision 3e549630b3f5120f1005c5e9752bf87f756afe49 (22 October 2026, before repair branch `fix/russ-computation-and-agda-reds-20261022`). Recompute CI and the generated SHA-256 inventory against the repair commit before treating any check as complete.

Computational interpretation

The canonical signature RussianRecursiveMathematicsBasis in FullCoupled/CanonicalLearnerMonolith.agda groups the selected Markov, ECT0, and Prop-valued countable-choice assumptions behind one named postulate. Its projections are not rewrite rules.

Markov principle. Theorem monolith functions russSearchBounded and russMarkovOperationalPrefix compute finite prefixes in increasing order. Result is either russSearchFound with a witness and evidence, or russSearchFuelExhausted. Exhaustion means only that the witness did not occur within the finite bound. An unbounded success claim still depends on the Markov assumption.

ECT0. russECT0CertifiedProgram exposes the exact basis projection. A program witness is paired with ComputesRelation evidence, including a finite ComputationTrace, machine steps, a halt witness, output, and relation evidence. Producing the program remains an application of the ECT0 postulate; it is not a reduction that compiles arbitrary relation data. The arithmetic representation bridge between register-machine traces and the object-language computation predicate is still an obligation.

Prop-valued countable choice. russPropCountableSelector exposes its proposition-valued interface. It does not extract erased evidence into a runtime function. By contrast, russDataCountableSelector aliases constructiveCountableChoice and computes a selector from already supplied SigmaWitness values.

Separate metatheoretic argument

For any actual basis B : RussianRecursiveMathematicsBasis, russSoundness interprets each RUSSDerivation in the denotation specified by B. Assumptions are interpreted by the context model; implication introduction extends the model; implication elimination applies the interpretation; each axiom tag maps to its corresponding B field. Falsehood denotes EmptyComputability, which has no constructors. In the empty context, context membership is impossible. Therefore any derivation of russFalsehood would, by soundness, produce an inhabitant of EmptyComputability, contradiction.

This is the formal theorem russCoreConsistency B : Neg (RUSSDerivation [] russFalsehood). russCurrentBasisRelativeConsistency instantiates it with the repository's postulated basis. Precise claim: conditional on an inhabitant of that basis, the small propositional object calculus has no derivation of false. This proof does not supply an independent model of the basis and does not prove consistency of the complete Agda development. Do not set fullRUSSConsistencyCertified to True.

A full certificate needs a model or relative-consistency proof for the exact combined dependent theory and its transitive import closure. It must cover: the selected MP encoding; ECT0's register-machine semantics and arithmetic representation theorem; compatibility of Prop-valued countable choice; actual imported theories; Reflection/TC primitives; rewrite rules with subject reduction and confluence; type interpretation, substitution, conversion and soundness; plus the checker/compiler trust boundary. Pédrot's MP model from 2020 and quotation-based Church-thesis work from 2024 are relevant research directions, not direct certificates for this repository's full mixture. Cockx, Tabareau, and Winterhalter show why rewrite confluence and subject reduction are essential. Keep the present certificate honest: lexical inventory is not a parser, and transitive closure plus global consistency remain unproved.

A* search verdict

The current Agda2HsSemanticSearch.agda is a dependency/capability planner, not a theorem-discovery system. SemanticLaw stores a name, capabilities, dependency-name list, and proposal prior. A* seeks a plan covering fixed requirements, then returns a SearchNode or Nothing. Its tests are meaningful for priority ordering, shortest paths, cycle rejection, dependency closure, repeated dependencies, and agreement of eager/deferred search. The e-graph saturates supplied expressions using supplied rewrite rules. These components can find a shorter plan within the encoded graph; they do not synthesize a proof term for a new theorem. The names in the example plan are supplied metadata, not Agda declarations. The empty-type regression is a Boolean test, not a consistency proof.

A theorem-discovery pipeline must generate conjecture candidates; search dependencies; synthesize a candidate Agda term; run Agda's checker with exact source and options; and record only accepted terms with source hashes, hypotheses, axioms, transitive dependencies, and minimized proof dependencies. Failed checks remain failed candidates. A* can rank or prune candidates; Agda checking, not the graph heuristic, establishes typeability relative to the trusted theory.

References

Stanford Encyclopedia of Philosophy, Constructive Mathematics:
https://plato.stanford.edu/entries/mathematics-constructive/

nLab, Russian constructivism:
https://ncatlab.org/nlab/show/Russian%2Bconstructivism

nLab, Markov's principle:
https://ncatlab.org/nlab/show/Markov%27s%2Bprinciple

Pédrot, 2020 syntactic presheaf model and Markov-principle result:
https://papertalk.org/papertalks/25451

Pédrot, 2024 Church-thesis paper:
https://lics.siglog.org/archive/2024/Pedrot-UponThisQuoteIWillB.html

Cockx, Tabareau, Winterhalter, The Taming of the Rew, POPL 2021:
https://popl21.sigplan.org/details/POPL-2021-research-papers/60/The-Taming-of-the-Rew

Haskell Wikibooks, denotational semantics:
https://en.wikibooks.org/wiki/Haskell/Denotational_semantics


Finite register-machine execution note

The canonical learner now defines runMachineFuel and runMachineWithFuel. Both are structurally recursive on a fuel bound. MachineRunResult distinguishes machineRunHalted from machineRunFuelExhausted. The refl regressions cover an immediate halt and a looping instruction whose fuel runs out. A halted evaluator result is still distinct from a ComputationTrace proof; ECT0's program witness must carry that trace and relation evidence.


Repair-branch regression findings (2026-10-22)

The pre-repair head fails both monolith checks at the same upstream name-clash: the unrenamed public Prelude import brings `Int` into scope before the local RUSS interface declares its own `Int`. Preserve the existing namespace contract by renaming Prelude's export to `PreludeInt`; keep the explicit local import of `Int` in `ConstructiveComputabilityPostulates`.

The same revision's extracted stream wrapper also rebinds `SIZEUNIV` after the selected dependency closure has already registered Agda's sized-type builtins. The stream module should consume `Size`, `Size<`, and `∞` via the public exports of `Haskell.Prim.Thunk`, not repeat compiler-owned `BUILTIN` bindings. This respects the project's Agda2HS import boundary.

The semantic-source-closure Scheme script had a missing closing parenthesis in its `.dot` argument predicate, so the conditional's expression boundary was malformed. Its syntax fix is independent of Agda proof validity.

The static-site JavaScript is a build-time renderer: it performs file I/O at the CLI boundary, whereas its mapping/escaping/string assembly are deterministic transformations and the generated page has no client-side JavaScript runtime. This is not a claim that the current Fennel utilities are globally pure or immutable; they still contain build-time I/O and some mutable local construction. A stricter purity guarantee needs to define and test the pure computational core separately from file/process effects.
