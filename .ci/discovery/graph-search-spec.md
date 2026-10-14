# Pure Agda2HS toolchain and graph-search contract

## Trust boundary

The supported pure extraction root is `FullCoupled.Agda2HsSemanticSearch`.
Its project-owned imports must stay within the Agda2HS-compatible subset and
`Haskell.Prelude`. The active flake must not fetch TypeTopology, add its source
to Agda's include path, or call a wrapper that silently adds it.

Generated Haskell is an explicit deliverable: keep readable `.hs` output, run
GHC with core lint, and record compiler, proof kernel, search implementation,
and source trust boundary in a manifest.

The two historical monoliths remain source-inspected during migration so
legacy theorem names can be inventoried. Text scanning does not type-check
those monoliths, validate their proofs, or transfer proof status. CI must not
say they were kernel-checked by the pure flake.

Acorn, XDS-Agda, and MiniVehicle are independent tools/checks. Acorn develops
proofs in its own language; it does not automatically import Agda proof terms.
XDS-Agda is a separate Agda development for denotational semantics. MiniVehicle
checks its own formalised language. Success in those checks is not a substitute
for this project's Agda type-check and extracted-Haskell compile.

## Three different graphs

1. **Agda module graph.** DOT vertices are modules; edges represent imports.
   This is not the law-dependency search and not an e-graph.
2. **Law dependency graph.** An edge `(source, target)` means the law named by
   `source` requires the law named by `target`. Search paths contain IDs, not
   Agda proof terms.
3. **Equational e-graph.** This stores equivalence classes of symbolic
   expressions. Congruence rebuilding, rewrite saturation, and best-expression
   extraction are separate from dependency-path search. A graph path is not an
   equational derivation.

## Path representation and maximality

A path is stored deepest dependency first; its head is the current/deepest node.
For adjacent IDs `child :: parent :: rest`, the path is valid only if `child`
occurs in `parent`'s dependency list. IDs may not repeat. Unknown IDs or
broken edges invalidate a path.

Expanding dependencies `[B, C]` from parent A produces sibling paths
`[B, A]` and `[C, A]`. Each sibling starts from the same parent path; a
sibling must never become an ancestor of the next sibling.

A path is maximal only when it is valid and its head node has no remaining
dependencies. A cycle such as A → B → A is not maximal. When cycle prevention
leaves no further child, that is a dead end, not success.

## Two distinct search routines

- `autonomousGraphSearchFromRoot` is bounded exhaustive DFS. Its depth bound
  is the number of laws. Since accepted paths contain no repeated ID, this
  bound covers every simple path. Its report must say DFS/maximal dependency
  chains, never A*.
- `graphAStarFirst` is a separate best-first single-plan search, with
  JAxtar's default discrete A* policy preserved. The root has `g=0`, each
  dependency edge costs one, and the heuristic is 0 for a leaf (or unknown
  node) and 1 for a node with dependencies. Its weighted score is the exact
  integer scaling of JAxtar's default `f = (1 - 10^-6)g + h`:
  `999999*g + 1000000*h`. A non-leaf needs at least one additional edge to
  reach a leaf, so `h=1` is a lower bound. Queue insertion uses `<=`, so an
  incoming equal-score node precedes an existing node.
- As in JAxtar's strict `optimal_mask` policy, a best-g table is keyed by the
  active law ID. Enqueue only when a candidate has a strictly lower g-cost;
  equal/worse duplicates are discarded and stale queue entries are skipped.
  The Agda version is a scalar list-based search, not JAxtar's batched JAX GPU
  implementation, hash table, or parent-array implementation. Its state,
  cost, score, deduplication, and tie-breaking policy are specified separately
  from implementation-level vectorization.
- Best-first search rejects repeated IDs and uses fuel `3 * factorial(n)`.
  Non-empty simple ordered paths are bounded by
  `sum(n!/(n-k)!, k=1..n) < 3*n!`. Fuel exhaustion returns `Nothing`; alone
  it is not a mathematical proof that no plan exists.
- A best-first result is one cheapest dependency chain for this cost, not a
  global proof-minimisation result. Search order, tie-breaking, and score are
  planning behaviour, not kernel rules.

## Required regression contract

Agda reduces these checks to `True`, and generated Haskell prints the same:

- `autonomousGraphSearchRegression`: linear A → B → C yields a valid plan.
- `graphDependencyOrderRegression`: A → [B, C] yields [B, A] and [C, A]
  without sibling leakage.
- `graphTwoLeafBranchesRegression`: enumeration returns both leaf paths for
  A → B and A → C.
- `graphCycleIsRejectedRegression`: A → B → A is not a maximal chain.
- `graphAStarTieBreakRegression`: equal-score insertion follows the
  incoming-first rule.
- `graphAStarBestGRegression`: only strictly cheaper duplicate states are
  enqueued, matching JAxtar's best-cost rule.
- Semantic-law and symbolic e-graph regressions remain separate.

The DOT parser is intentionally narrow: it accepts lines whose first three
whitespace-delimited tokens are `source -> target`; it strips surrounding
quotes and trailing semicolons. It is not a general Graphviz parser. Node
attributes, subgraphs, quoted names containing spaces, and multi-line
declarations are unsupported until separately regression-tested.

## Migration exit criteria

The active flake has no TypeTopology input/include path; type-checks the pure
Agda2HS modules; retains readable Haskell; compiles it with GHC core lint; runs
graph/e-graph regressions; marks historical monoliths source-inventory-only;
and runs Acorn, XDS-Agda, MiniVehicle independently. Claim a green result only
after CI reports success.
