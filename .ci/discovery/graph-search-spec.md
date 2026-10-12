# Pure Agda2HS toolchain and graph-search contract

## Trust boundary

The supported, type-checked source root for the pure extraction path is
`FullCoupled.Agda2HsSemanticSearch`. Its project-owned imports are restricted
to the Agda2HS-compatible subset and `Haskell.Prelude`. The flake must not
fetch TypeTopology, add its source to Agda's include path, or call a wrapper
that silently adds it.

Generated Haskell is an explicit deliverable, not an opaque compiler by-product:
the build keeps each generated `.hs` file, runs GHC with core lint, and records
the compiler, proof kernel, search implementation, and source trust boundary in
a manifest.

The two historical monoliths remain source-inspected during the migration so
legacy theorem names can still be inventoried. Source scanning does not type
check, validate, or transfer proofs from those monoliths. No CI report may
describe them as kernel-checked by the pure flake.

Acorn, XDS-Agda, and MiniVehicle are independent tools/checks. Acorn checks
Acorn-language developments; it does not automatically import Agda proof terms.
XDS-Agda is a separate Agda development for denotational semantics. MiniVehicle
checks its own formalised language and normalisation results. Their successes
are not a substitute for compiling this project's generated Haskell or
type-checking this project's Agda modules.

## Three different graphs

1. **Agda module graph.** Agda emits a DOT import-dependency graph for the pure
   root module. Its vertices are modules and its edges are import relations.
   It is not the theorem-dependency search and not an e-graph.
2. **Law dependency graph.** An edge `(source, target)` means that the law
   named `source` requires the law named `target`. Each node has a stable law
   identifier and an ordered list of dependency identifiers. Search paths
   contain identifiers, not Agda proof terms.
3. **Equational e-graph.** The e-graph stores equivalence classes of symbolic
   expressions; congruence rebuilding, rewrite saturation, and best-expression
   extraction are separate from dependency-path search. A graph path is not an
   equational derivation.

## Dependency-path representation

A path is stored deepest dependency first; its head is the current/deepest node.
For adjacent identifiers `child :: parent :: rest`, the path is valid only if
`child` occurs in `parent`'s dependency list. Identifiers may not repeat.
Unknown identifiers or broken edges invalidate a path.

Expanding a node with dependencies `[B, C]` yields sibling paths
`[B, parent, ...]` and `[C, parent, ...]`. The parent path is unchanged while
each sibling is formed. A previously discovered sibling must never become an
ancestor of the next sibling.

A path is **maximal** only when it is valid and its head node has no remaining
dependencies. A cycle such as A → B → A is not a terminal/maximal path, even
when cycle prevention means no further child can be added. A stuck cyclic or
malformed path is a dead end, not success.

## Two path-search routines; do not conflate them

- `autonomousGraphSearchFromRoot` is a bounded exhaustive depth-first
  enumerator. Its depth bound is the number of laws. Because accepted paths
  contain no repeated identifier, this bound is enough for any simple path.
  It returns the sorted set/list of maximal paths reached from the root. Its
  report must call this DFS/dependency-chain enumeration, never A*.
- `graphAStarFirst` is the separate best-first single-plan search. Its cost is
  `g(path) = length(path)`. The heuristic is 0 for a leaf (and for an unknown
  node) and 1 for a node with at least one dependency. This is an admissible
  lower bound because every non-leaf requires at least one more edge to reach
  a leaf. Insertion uses `<=`, so an incoming equal-score node precedes the
  existing node; that tie behaviour is regression-tested.
- The best-first search prevents repeated identifiers and uses a finite fuel
  bound of `3 * factorial(numberOfLaws)`. For n unique law IDs, the number of
  non-empty simple ordered paths is bounded by
  `sum(n!/(n-k)!, k=1..n) < 3*n!`. Exhausting fuel returns `Nothing`; it is
  not evidence that no mathematical plan exists unless the finite-search
  bound and graph assumptions have been established.
- The best-first result is one cheapest dependency chain according to this
  guidance cost. It is not a global proof-minimisation result. Search order,
  tie-breaking, and score are heuristic planning behaviour, not kernel rules.

## Required regression contract

Agda must reduce the following booleans to `True`, and the generated Haskell
runner must print the same values:

- `autonomousGraphSearchRegression`: a linear A → B → C graph has a valid plan.
- `graphDependencyOrderRegression`: A → [B, C] generates two sibling plans,
  [B, A] and [C, A], without leaking B into C's path.
- `graphCycleIsNotMaximalRegression`: A → B → A cannot be accepted as a
  maximal dependency chain.
- `graphAStarTieBreakRegression`: equal-score insertion is stable according
  to the documented incoming-first rule.
- Existing semantic-law completeness and symbolic e-graph regression outputs
  remain separate assertions and must continue to run.

The DOT parser is currently intentionally narrow: it accepts lines whose
first three whitespace-delimited tokens are `source -> target`. It strips
surrounding quotes and a trailing semicolon. It is not a general Graphviz
parser. Node attributes, subgraphs, quoted names containing spaces, and
multi-line declarations are outside the accepted input grammar until covered
by additional regression fixtures.

## Exit criteria for the migration

The pure flake must: (1) have no TypeTopology input or TypeTopology include
path; (2) type-check the four Agda2HS modules; (3) extract readable Haskell;
(4) compile generated code with GHC core lint; (5) run search and e-graph
regressions; (6) report legacy monoliths only as source-inventory inputs; and
(7) execute the Acorn, XDS-Agda, and MiniVehicle checks as independent lanes.
A green result is claimed only after CI actually reports success.
