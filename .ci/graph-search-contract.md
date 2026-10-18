# Graph search contract

## 1. Input and direction

Input is a finite list of directed edges `(source, target)`. For a DOT theorem dependency graph, `source -> target` means “source depends on target.” The graph builder records `target` as a direct dependency of `source`.

A path is stored with the current/terminal node first, followed by its dependencies. Thus edges `A -> B` and `B -> C` produce chain `[C, B, A]`. This direction must remain stable in fixtures and reports.

## 2. Data model

- `GraphLaw`: unique law/node identifier plus the list of direct dependencies.
- `GraphNode`: a path of identifiers in deepest/current dependency-first order.
- `graphLawsFromEdges`: reconstructs the direct-dependency lists from edge pairs.
- `graphExpandNode`: expands the head of a path using that node's direct dependencies.
- `graphValidPlan`: requires a nonempty path, unique identifiers, and a valid dependency edge between every adjacent child/parent pair.
- `graphMaximalDependencyChain`: accepts a valid path when all direct dependencies of its head are already present in the path. This is maximality for a **simple path**, not proof that the whole graph is acyclic or that a theorem is true.

Identifiers are unique by exact string equality. Missing dependency identifiers must not be invented into a valid path. Cycles stop when an expansion points to an identifier already in the current path.

## 3. Expansion rule (critical invariant)

For current path `p` and each direct dependency `d` of its head, produce a child path `d :: p` **from the same unchanged parent path `p`**. One sibling must never become the parent of the next sibling.

The recursive accumulator may collect each child, but recursion over the sibling list must retain original `p`:

```agda
graphExpandDependencies (dependency ∷ dependencies) plan acc =
  if graphContains dependency plan then
    graphExpandDependencies dependencies plan acc
  else
    graphExpandDependencies
      dependencies
      plan
      (graphNode (dependency ∷ plan) ∷ acc)
```

The former behavior recursed with `(dependency ∷ plan)`, causing later siblings to inherit an earlier sibling and fabricating edges such as `[C, B, A]` for independent edges `A -> B` and `A -> C`. The regression `graphTwoLeafBranchesRegressionChecked` and existing `graphDependencyOrderRegressionChecked` lock down the fix. Input dependency order remains stable because the accumulator is reversed once at the end.

## 4. Two separate search modes

Do not call every traversal “A*”.

### `graphAStarFirst`: one best-first maximal chain

- Seed: one initial `GraphNode`.
- Path cost: `g(n) = length(path)`; a singleton seed starts at one, and each dependency extension adds one. This has the same ordering as edge-count cost from the fixed seed because the seed-prefix contribution is constant.
- Heuristic: `h(n) = 0` when the current head has no dependencies; otherwise `h(n) = 1`.
- Priority: the JAxtar-compatible integer score `999999*g(n) + 1000000*h(n)`, an exact integer scaling of `(1 - 10^-6)g + h`. Insertion places an equal-score candidate before an older entry (`<=`).
- Goal: first `graphMaximalDependencyChain` accepted from the ordered frontier.
- Fuel: `3 * factorial(number of graph laws)`. This is the explicit finite simple-path search bound for the current implementation. Exhaustion returns `Nothing`; callers must preserve that result, not convert it to success.

The heuristic is intentionally small and only supports current best-first ordering. Do not claim a general shortest-path optimality theorem without proving that the heuristic and goal definition satisfy A* assumptions.

### `autonomousCanonicalGraphSearch`: bounded enumeration

- Parses DOT edges and begins at `FullCoupled.Agda2HsSemanticSearch`.
- Expands with `graphSearchDepth` / `graphSearchChildren`, bounded by number of graph laws.
- The explicit `autonomousCanonicalGraphSearch` routine enumerates maximal simple dependency chains and sorts them by path length. Equal-length ordering follows the stable insertion behavior of `graphInsertPlan`.
- Production report counts do **not** materialize that path list. For an acyclic graph, `autonomousGraphSearchCount` and `autonomousCanonicalGraphSearchCount` use a topological dynamic-programming table: a leaf contributes one chain, and each other node contributes the sum of its direct dependencies' counts. The whole-graph report sums per-node counts; the canonical report reads the root count. This keeps exact counts without exponential path enumeration and quadratic sorting.
- If the input is not topologically sortable, counters fall back to the existing fuel-bounded simple-path enumeration, preserving cycle behavior.
- Report label remains `agda2hs autonomous theorem-graph DFS: N maximal dependency chains`.

This enumeration is bounded DFS, not `graphAStarFirst`. Its report must not say “A*”. The explicit enumeration routine remains useful for small regression fixtures; report counting uses dynamic programming on the Agda module DAG. `graphAStarFirst` selects one chain for a supplied goal/root.

Neither routine proves that a theorem represented by a graph node is valid. A dependency path is a navigation artifact, not a proof term.

## 5. Regression contract

All fixtures should be checked by Agda reduction (`...Checked = refl`) before extraction, and then remain in the Nix semantic lane.

1. **Linear chain:** `A -> B`, `B -> C` includes `[C, B, A]`.
2. **Two independent leaves:** `A -> B`, `A -> C` returns exactly `[B, A]` and `[C, A]`; it must not return `[C, B, A]`.
3. **Unique identifiers:** duplicate identifiers cannot appear in one path.
4. **Dependency order:** each adjacent path pair must be justified by the parent's direct dependency list.
5. **Cycle policy:** a back-edge into the current path stops expansion. Current tests deliberately treat the simple path as maximal; they do not certify the input graph is acyclic.
6. **Tie policy:** `graphAStarTieBreakRegressionChecked` locks down equal-score insertion order.
7. **Fuel exhaustion:** missing goal/invalid graph or exhausted finite budget yields `Nothing`, not an invented result.
8. **Generated source:** DOT parser regressions cover qualified quoted names, semicolons, attribute suffixes, and malformed non-edge lines.
9. **Duplicate-heavy closure:** repeated dependency entries must not exhaust closure fuel before the queue drains.
10. **Input normalization:** duplicate arrows yield one dependency and one branch; self-loops fail as leaf searches.
11. **Multi-parent DAG:** both parent branches remain valid; A* returns one shortest, valid branch.

## 6. Required next hardening

- Add a stable graph artifact schema containing format version, source commit, node count, edge count, and hash. Keep theorem proof checking separate from graph generation and graph search.
- Extend the narrow DOT parser only when fixtures cover the new syntax; quoted names containing spaces and multi-line declarations remain unsupported.
- Compare fixtures against the legacy Mercury search only as a differential compatibility oracle. Do not restore the Mercury runtime or assert behavioral equivalence until selected outputs and budgets are captured and matched.
