# Viktor Csimma's Agda2HS work: source and paper review

Date: 2026-11-21

Scope: primary-source review for PR #335. This note covers the papers and public repositories directly named in Csimma's 2026 Agda2HS/Agdalache paper, the Acorn exact-real project, the Agdalache/EvenCounter examples, the Agda2HS pull requests authored by Csimma that materially affect source imports, erasure, names, or Haskell interop, and the current learner import/configuration surface. This is a source-repository review, not binary/runtime reverse engineering.

## Primary sources

- Csimma, *Adapting the MVVM pattern to C++ frontends and Agda-based backends* (JFP, 2026): https://arxiv.org/pdf/2603.24199 and https://jfp.episciences.org/en/articles/18962
- Csimma, *Acorn – an agda2hs-compatible representation of exact real arithmetic* (2023): https://csimmaviktor.web.elte.hu/acorn.pdf
- Agda2HS source: https://github.com/agda/agda2hs
- Csimma repositories:
  - https://github.com/viktorcsimma/agdalache
  - https://github.com/viktorcsimma/even-counter
  - https://github.com/viktorcsimma/acorn
  - https://github.com/viktorcsimma/acorn-calc
  - https://github.com/viktorcsimma/benchmarks
  - https://github.com/viktorcsimma/bishop (the `agda2hs` branch)

## 1. Findings from the 2026 paper

### Agda2HS model

Agda2HS intentionally extracts a Haskell-compatible sublanguage, not arbitrary Agda. Runtime dependent data must be erased; proof-only arguments and fields are marked `@0`. Csimma's EvenCounter example makes this concrete: a proof function is erased, and an `S0` package carries a runtime value while erasing its proof field. See paper §2 and §4.1, and `agdalache/backend/src/Tool/ErasureProduct.agda`.

### Haskell dependencies: Csimma's ranked approaches

Paper §5.2 distinguishes several techniques:

1. Put the affected implementation entirely in a `FOREIGN AGDA2HS` block. This is simple but infective: dependent definitions also need to move into foreign code, losing Agda proof leverage.
2. Postulate a single Agda function and provide its Haskell implementation in a foreign block. Good for one-off dependencies.
3. Postulate the Haskell API and give its implementation once in a foreign block. Useful when reused within a module, but adds boilerplate per imported symbol.
4. Put wrappers in `Haskell.*` modules. Since Agda2HS PR #379, such modules are treated as Haskell-side FFI modules: the `Haskell.` prefix is removed, no ordinary generated Haskell module is emitted, and the corresponding native Haskell module is imported. This is the preferred reusable boundary for repeated dependencies.
5. Add common interfaces to agda2hs-base only when they have general value to the compiler community.
6. Use YAML rewrite rules for translating names from a large Agda library to Haskell names. Csimma notes that this has no typechecking of the replacement mapping and duplicates information; it is mainly useful when retaining a proof dependency on a library that is not agda2hs-compatible.

Neither Agdalache nor Acorn should be read as saying that every FFI module is appropriate for a pure numerical core. The IORef, StablePtr, C types, pointers, Storable, MVar, CFuture, GHC concurrency, C strings, and platform modules are application integration layers.

### Benchmark claims and limits

Paper §7 benchmarks two synthetic workloads (natural-number evaluation and binary-tree evaluation) on one AMD Ryzen 7 3700U machine. It reports translation, GHC compilation, and runtime separately. Agda2HS is often around twice as fast as MAlonzo in the tested compilation/translation measures; Rocq's OCaml extraction is substantially faster at translation and compilation. Runtime comparisons vary by workload: Agda2HS is competitive on the tree workload, while Rocq is much faster on large natural-number iteration. GHC `-O1` often improves Agda2HS runtime.

The paper itself lists important threats to validity: only two dummy tasks, one personal machine, and unexplained workload-dependent differences. This is evidence that Agda2HS is viable, not evidence that this learner's GRU/CHAD kernels are fast. The learner needs its own extracted-Haskell benchmarks and parity tests.

### Agdalache architecture

The paper's MVVM advice is about a GUI application boundary: a backend-owned model, stable application state, and C/C++ view-model integration. It is not a requirement that the pure learner import the toolkit. The paper explicitly identifies Agdalache as an SDK around Agda/Haskell backends and C++ Qt frontends.

## 2. Findings from Acorn (2023 paper and GitHub)

Acorn is a useful numerical design reference, but it is not a direct implementation template for the Q12.20 learner.

- Its real-number design follows Krebbers–Spitters approximate rationals and O'Connor's completion monad.
- The abstraction `AppRationals` needs approximate division and precision-controlled approximation; real values are represented through a completion of an approximate-rational space.
- The concrete dyadic representation is a pair `mant : Int` and `expo : Int`, interpreted as mantissa times a power of two. Addition aligns exponents; multiplication multiplies mantissas and adds exponents.
- The implementation uses arbitrary-precision Haskell `Integer` rather than a bounded Q-format. Its integer layer maps to Haskell builtins and uses hand-written foreign alternatives for performance-sensitive operations, including `Data.Bits.shift`.
- `Function.SquareRoot` uses Newton iteration with precision-dependent approximate division.
- The code uses `FOREIGN AGDA2HS` extensively and includes many `cheat` proofs/postulates. Csimma's 2023 paper explicitly calls this a running-first strategy and warns that the missing proofs and possible mathematical errors remain work.
- The paper's 2023 speed tests compare selected exact-real workloads against Krebbers' Haskell implementation; Acorn is sometimes faster and sometimes slower. This is a separate experiment from the 2026 Agda2HS compiler benchmark.

Useful transfer: precision-aware approximation, dyadic scaling, explicit optimized Haskell primitives, and measuring generated code. Non-transferable without redesign: arbitrary-precision exact reals, completion monad, unbounded `Integer`, broad algebraic typeclass hierarchy, and GUI shell/FFI dependencies.

## 3. Source modules inspected

### Agdalache and EvenCounter

Inspected source includes:

- `backend/src/All.agda`: separates modules imported for Agda typechecking from the explicit `FOREIGN AGDA2HS` list of Haskell modules to compile/link. This is an important distinction: typechecking imports and generated-Haskell imports are not identical.
- `AppState.agda`: imports `Haskell.Prelude` and `Haskell.Data.IORef`; mutable GUI state is behind IORefs.
- `Interaction.agda`: imports IORef, StablePtr, Ptr, C.Types, CFuture, application logic, and foreign helpers. This is C integration, not pure model code.
- `Tool.ErasureProduct.agda`: defines `S0` with an erased proof field and `S'` with an erased dependency in a type-level function; both have Agda2HS compile pragmas.
- `Tool.PropositionalEquality.agda`: proof-only `cong`, `sym`, `trans`, and `subst`, all marked `@0`.
- `Tool.Relation.agda`: universe-polymorphic disjunction and erased relation predicates; imports `Agda.Primitive`, `Haskell.Prim.Tuple`, and `Haskell.Prim`'s bottom type.
- `Haskell.Data.IORef.agda`: postulated Haskell IORef interface.
- `Haskell.Control.Concurrent.CFuture.agda`: CFuture adapter built on MVar, StablePtr, Ptr, Storable, GHC concurrency, and foreign helpers.
- `Tool.Foreign.agda`: C type conversions, C strings, platform semaphore/event calls, and StablePtr convenience wrappers.
- `EvenCounter/backend/src/Logic.agda`: imports builtin Nat/Int and `Haskell.Prelude`; proves evenness with erased proofs and `S0`; supplies foreign Haskell `even` implementations. This is the clearest example for erased Nat indices and value/proof separation.

### Acorn

Inspected the module aggregator and central numerical/application modules:

- `src/All.agda`: imports the broad mathematical and shell project for Agda typechecking, then explicitly lists the Haskell modules to include in a generated aggregate. Several proof-only modules are deliberately excluded from the Haskell list.
- `src/Implementation/Dyadic.agda`: concrete `mant :|^ expo` representation; exponent alignment for addition; product exponent addition; fast comparisons; Haskell foreign overrides; many proof obligations still use `cheat`.
- `src/Implementation/Int.agda`: Agda builtin Int with a Haskell `Integer` representation, explicit foreign implementations for arithmetic, quotient/remainder and abs; uses `Data.Bits` in the foreign Haskell boundary.
- `src/Implementation/Frac.agda`: generic fraction representation with erased denominator nonzero proof; broad algebraic instances, many unfinished proofs.
- `src/Implementation/Rational.agda`, `src/Implementation/Nat.agda`, `src/RealTheory/AppRational.agda`, `src/RealTheory/Completion.agda`: core approximate-rational/completion architecture. Completion is a regular-function representation with erased regularity proofs; operations require continuity/modulus information.
- `src/Function/SquareRoot.agda`: Newton iteration over approximate rationals, using precision-aware division and dyadic shifts.
- `src/Shell/Interaction.agda`: shell and C interface. It is explicitly foreign-heavy and imports IORef, StablePtr, CString, C types, concurrency, exceptions, NFData, platform and parser modules.
- `src/Tool.Cheat.agda`: erased postulate used to defer proof completion.
- `src/HaskellInstance/Num.agda` and `Floating.agda`: Haskell typeclass adapters; Floating is written in a foreign block and has unimplemented operations. This is not a requirement for the fixed-point learner.

Acorn's import set is intentionally broad because it is a full exact-real library and calculator. It must not be copied wholesale into the learner monolith.

### Bishop agda2hs branch

Inspected `bishop/agda2hs` branch files include `Real.agda`, `ErasureProduct.agda`, `FastPow.agda`, `NonReflective*.agda`, `RewriteRules.yaml`, and `Test.agda`. This branch is an intermediate experiment built around Agda standard-library proofs plus rewrite rules, not the same import policy as Acorn's later agda2hs-base implementation. Its YAML rewrite configuration maps stdlib Nat/Int/Rational identifiers and operations into Haskell Prelude or custom modules. It demonstrates the intended use of the Agda2HS YAML rewrite facility, but it is not a reason to add stdlib imports into the current agda2hs-base project.

### Other repositories

- `acorn-calc` is the C++ Qt frontend; its value here is integration context, not Agda learner imports.
- `benchmarks` contains the benchmark programs referenced by the 2026 paper; they are compiler/extraction benchmarks, not RL learner benchmarks.

## 4. Csimma-authored Agda2HS pull requests reviewed

Relevant merged/closed PRs found through GitHub search:

- #183: marks `Num` applicability-condition fields erased.
- #184: proposes translating builtin Nat zero patterns to Haskell numeric literal zero; the PR is closed and has no merge timestamp, so do not assume this proposal is in the pinned compiler.
- #186: filters erased local function definitions from generated Haskell.
- #187: allows type operators that do not start with a colon.
- #189: introduces YAML name-rewrite rules.
- #193: configures Prelude import behavior (`implicit`, `hiding`, `using`).
- #195: erases value arguments in type-level functions and record/type-lambda parameters.
- #258: adds `Haskell.Prim.the` for explicit Haskell type signatures.
- #291: proposes a `Haskell.Data.Map` interface.
- #297: introduces Haskell.Data/Haskell.Control prefix mapping; superseded by #379.
- #298: Alternative interface; depends on the module-prefix feature.
- #299: Data.Char cognates.
- #300: skips up-to-date generated modules.
- #379: merged replacement for #297; any `Haskell.*` module is treated as a Haskell-side FFI module with the prefix removed.

Also found #198, #209, and #261 for Emacs integration/documentation; not relevant to learner imports or runtime semantics.

## 5. Consequences for PR #335

### Keep

The current canonical file's broad shape is consistent with the Csimma examples:

- `Haskell.Prelude` as the agda2hs-base programming surface.
- `Agda.Primitive` only for the universe names the monolith actually uses.
- Local erased proof/equality/relation definitions rather than importing application-local `Tool.*` modules.
- The Agda 2.9 erased-logic builtins only because the monolith's options/use require them.
- `Agda.Builtin.Equality.Rewrite` only because the monolith declares Agda rewrite rules.

### Important distinction: two different rewrite systems

Do not conflate:

1. Agda's builtin rewrite mechanism: `Agda.Builtin.Equality.Rewrite`, `{-# REWRITE ... #-}`, and Agda confluence checking. This is what the monolith's source currently uses.
2. Agda2HS YAML name-rewrite rules: Csimma PR #189 and the `--rewrite-rules` configuration, used to map Agda qualified names to Haskell names/modules. The current `.ci/agda/agda2hs.yaml` only configures Prelude (`implicit: true`, hiding `seq`); it contains no name-rewrite rules.

The presence of `Agda.Builtin.Equality.Rewrite` does not enable Csimma's YAML rewrite feature, and YAML rewrite rules do not replace Agda's proof rewrite declarations.

### Do not import

For the pure learner, do not import Csimma's GUI/runtime integration modules merely to be "faithful": IORef, StablePtr, Ptr, Storable, C.Types, CFuture, MVar, GHC.Conc, Tool.Foreign, Platform.Posix/Win32, CString, parser/shell, NFData/Floating adapters. Add a specific Haskell-side module only when a concrete runtime primitive needs it and its import path has been verified against the pinned Agda2HS version.

### Numerical design

Acorn is an algorithmic reference for dyadic scale management and Newton refinement, not an endorsement of unbounded `Integer` or floating point for this project. Keep Q12.20 fixed-width arithmetic and Int64 intermediates as the learner's runtime contract; use Acorn-style high-precision or exact arithmetic only as an independent reference oracle in tests/proofs. Measure extracted kernels rather than extrapolating from Csimma's generic compiler benchmarks.

## 6. Verification status and limits

- This review inspected the cited papers, repository trees, selected central Agda source files, the named Agda2HS PR diffs, and the current PR #335 source/config.
- It did not run Agda2HS, GHC, QuickCheck, or the learner's CI. No performance or typechecking claim is made for PR #335.
- The Acorn source has many `cheat` obligations and foreign implementations; treat it as a design/performance reference, not a completed proof artifact.
- REA is intended for shipped binaries/runtime artifacts. The current investigation is ordinary source-repository analysis through GitHub; no REA engine/tool was available or needed.
- Swift Concurrency is not applicable to the Agda/Lua Lanes code in this repository; do not introduce Swift actors/tasks as an unrelated abstraction.
- Smart Model Router is a separate Windows Codex task window and cannot change the model powering this ChatGPT conversation. No model switch or local Windows launch was performed.
- CubbyEd's Logic-stage material is useful as a pedagogical analogy for premises, conclusions, and proof structure, not as a software dependency or source of technical facts.
