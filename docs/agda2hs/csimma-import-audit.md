# Viktor Csimma Agda2HS Import-Family Audit

## Purpose and interpretation

This is an **audit of import families**, not a directive to import every module. Strict confinement means every family is classified and justified; the learner imports only the smallest surface needed by its pure integer semantics and actual extraction seam.

The inspected Csimma examples are `viktorcsimma/agdalache` and `viktorcsimma/even-counter`. Their adapter graph is a methodology reference, not a dependency list for this learner.

## Current branch evidence

`chore/canonical-learner-builtin-imports` currently contains a 43-line file with:
- `open import Haskell.Prelude public`
- a Haskell foreign block importing `Data.Bits`, `Data.Int (Int64)`, `Data.Word (Word64)`, and `Data.Vector.Unboxed`.

The comment in that file explicitly acknowledges that the agda2hs Prelude re-exports `Double`. This violates the no-floating-import/type requirement. The file has no learner definitions, no postulates, no erased `S0` witness, and no GRU/SARSA/FQF implementation.

The default `main` file is a 548-line older learner prototype. It imports:
- `Agda.Primitive`
- `Haskell.Prim`
- `Haskell.Prelude`
- `Haskell.Laws`
- `Haskell.Prim.Thunk`
- `Agda.Builtin.Erased.Funext`
- `Agda.Builtin.Erased.Propext`
- `Agda.Builtin.Erased.Quotient`

It contains a floating-era LSTM implementation and is not the requested target. Do not copy its broad import surface or recurrent architecture wholesale.

## Family classification

| Family / module | Classification | Rationale |
|---|---|---|
| `Agda.Primitive` | Conditional | Import only exact universe names actually used in the canonical source. Avoid a broad public re-export. |
| `Haskell.Prim` | Conditional, preferred primitive source | Use selective names for Agda2HS-compatible primitive types/constructors required by generated Haskell. Verify exact exports against the pinned agda2hs library before editing. |
| `Haskell.Prelude` | Excluded from learner public surface | It re-exports a broad Haskell-facing prelude, including `Double` per the current branch comment. A no-float contract cannot rely on a broad re-export. |
| `Haskell.Laws` | Excluded unless a concrete law is used | No observed learner symbol requires this import. Proofs should use the exact equality/relations required, not a blanket law module. |
| `Haskell.Prim.Thunk` | Excluded unless an actual delayed/coinductive value is present | No observed learner symbol uses `Thunk`; laziness of extracted Haskell does not justify importing this module. |
| `Agda.Builtin.Equality` | Conditional / likely allowed | Use only for equality proofs actually present. |
| `Agda.Builtin.Equality.Rewrite` | Conditional | Keep only if rewrite rules are declared and required. Merely enabling `--rewriting` or importing the module does not establish need. |
| `Agda.Builtin.Erased.*` | Excluded unless exact erased primitive is used | The repository enables erasure globally; this alone does not require explicit imports of erased funext, propext, or quotient modules. |
| `Tool.ErasureProduct` (`S0`, `S'`) | Conditional / allowed for proof packaging | Retain a minimal erased simulation witness only when the canonical module actually constructs or consumes it. |
| `Tool.PropositionalEquality` | Conditional | Import only if its exact proof interface is required; builtin equality may suffice. |
| `Tool.Relation` | Conditional | Import only for relation-level proof structure actually used. |
| `Haskell.Data.IORef` | Excluded from pure learner | Mutable references are not part of the pure recurrent/learner kernel. |
| `Haskell.Prim.IO` | Excluded from pure learner | IO is not part of the learner semantics. |
| `Haskell.Foreign.Ptr` | Excluded | No pointer-valued learner interface exists. |
| `Haskell.Foreign.StablePtr` | Excluded | No stable-pointer lifetime or callback interface exists. |
| `Haskell.Foreign.C.Types` | Conditional, only at a real C ABI seam | Fixed-width Haskell `Int32`/`Int64` can be imported in the FFI block directly when no C ABI type is exposed. |
| `Haskell.Foreign.C.String` | Excluded | No C string interface exists. |
| `Haskell.Foreign.Storable` | Excluded | No `Storable` pointer-marshalling interface exists. |
| `Haskell.Control.Concurrent.MVar` | Excluded | No shared mutable concurrency in the pure learner. |
| `Haskell.Control.Concurrent.CFuture` | Excluded | No C future/event callback seam exists. |
| `GHC.Conc` | Excluded | Runtime concurrency primitives are outside the pure learner. |
| `Tool.Foreign` | Conditional, adapter-only | Use only when a real foreign function is declared; keep it out of pure Agda semantics. |
| `Platform.Win32` / `Platform.Posix` | Excluded from core | Platform-specific adapters belong in an executable shell, not the learner module. |
| `Data.Bits` | Allowed in narrow Haskell FFI block | Required for integer shifts/masks/bit operations; no floating capability. |
| `Data.Int` | Allowed in narrow Haskell FFI block | Fixed-width integer representation. |
| `Data.Word` | Conditional | Use only if unsigned bit reinterpretation or PRNG state requires it; prove conversion semantics. |
| `Data.Vector.Unboxed` | Conditional / likely allowed | Use only if the learner actually uses unboxed vectors; bounds and index conversions must be explicit. |
| `Control.Parallel.Strategies` | Excluded | No parallel evaluation is required; it adds runtime scheduling and a larger trust surface. |

## Strict import rules

1. No `Haskell.Prelude` blanket import in the learner.
2. No `Double`, `Float`, `Rational`, floating literal, or floating conversion in Agda or generated Haskell.
3. Import only exact names used; prefer `using (...)` / `hiding (...)` supported by the pinned library.
4. Every `postulate` must have a matching foreign implementation or be explicitly identified as an axiom with a proof/trust rationale.
5. Every `COMPILE AGDA2HS` mapping must be checked against generated Haskell.
6. Keep IO, mutable references, pointers, stable pointers, C strings, Storable, MVars, futures, GHC concurrency, and platform adapters out of the pure learner.
7. Do not add all Csimma modules merely to claim coverage. Coverage is the classification table plus a mechanically checked minimal selected import surface.

## Required mechanical audit

Before merge:
- Search Agda source and extracted Haskell for `Float`, `Double`, `fromRational`, floating literals, and floating conversions.
- Search imports for every excluded adapter family above.
- Enumerate every Agda `postulate` and match it with a foreign implementation or explicit trust note.
- Inspect generated Haskell from the actual canonical Agda module.
- Run Agda typecheck and full CI.

## Open verification item

The exact selective export names from the pinned Agda2HS `Haskell.Prim` library must be read from the version selected by `flake.lock` / `flake.nix`. This audit intentionally does not invent an import list before that source is inspected.
