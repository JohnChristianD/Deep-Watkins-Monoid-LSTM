module FullCoupled.Agda2HsGraphSearchCheck where


open import Haskell.Prelude
import FullCoupled.Agda2HsSemanticSearch as Search

-- This checker imports only the Agda2HS runtime modules. It does not import
-- TheoremsMonolith or any TypeTopology module.
graphSearchContractPassed : Bool
graphSearchContractPassed =
  Search.graphDependencyOrderRegression
    && Search.graphTwoLeafBranchesRegression
    && Search.graphAStarTieBreakRegression
    && Search.graphAStarBestGRegression
    && Search.graphAStarShortestPathRegression
    && Search.graphAStarDeferredPriorityLowerBoundRegression
    && Search.graphAStarDeferredMatchesEagerRegression
    && Search.multiCapabilityCoverageRegression
    && Search.nodeHeuristicLowerBoundRegression
    && Search.graphCycleIsRejectedRegression
    && Search.graphDependencyClosureRegression
    && Search.graphPathCountRejectsCycleRegression
    && Search.graphDependencyClosureRejectsCycleRegression
    && Search.graphDependencyClosureRejectsMissingRegression
    && Search.graphDependencyClosureRepeatedDependenciesRegression
    && Search.graphDuplicateEdgeSearchRegression
    && Search.graphMultiParentSearchRegression
    && Search.graphSelfLoopRejectedRegression
    && Search.graphDotParserRegression
    && Search.learnerLogicalGraphRegression
    && Search.learnerSemanticBridgeRegression
    && Search.autonomousGraphSearchRegression
    && Search.canonicalSearchPlanEGraphClosed
    && Search.graphAStarPlanEGraphClosed

main : IO ⊤
main = do
  putStrLn
    ("graph-dependency-order="
      ++ show Search.graphDependencyOrderRegression)
  putStrLn
    ("graph-two-leaf-branches="
      ++ show Search.graphTwoLeafBranchesRegression)
  putStrLn
    ("graph-best-first-tie="
      ++ show Search.graphAStarTieBreakRegression)
  putStrLn
    ("graph-best-g-policy="
      ++ show Search.graphAStarBestGRegression)
  putStrLn
    ("multi-capability-coverage="
      ++ show Search.multiCapabilityCoverageRegression)
  putStrLn
    ("graph-admissible-heuristic="
      ++ show Search.nodeHeuristicLowerBoundRegression)
  putStrLn
    ("graph-cycle-rejected="
      ++ show Search.graphCycleIsRejectedRegression)
  putStrLn
    ("graph-closure-diamond="
      ++ show Search.graphDependencyClosureRegression)
  putStrLn
    ("graph-path-count-cycle-rejected="
      ++ show Search.graphPathCountRejectsCycleRegression)
  putStrLn
    ("graph-closure-cycle-rejected="
      ++ show Search.graphDependencyClosureRejectsCycleRegression)
  putStrLn
    ("graph-closure-missing-rejected="
      ++ show Search.graphDependencyClosureRejectsMissingRegression)
  putStrLn
    ("graph-closure-duplicate-dependencies="
      ++ show Search.graphDependencyClosureRepeatedDependenciesRegression)
  putStrLn
    ("graph-duplicate-edge-normalization="
      ++ show Search.graphDuplicateEdgeSearchRegression)
  putStrLn
    ("graph-multi-parent-dag="
      ++ show Search.graphMultiParentSearchRegression)
  putStrLn
    ("graph-self-loop-rejected="
      ++ show Search.graphSelfLoopRejectedRegression)
  putStrLn
    ("graph-dot-parser-regression="
      ++ show Search.graphDotParserRegression)
  putStrLn
    ("graph-astar-shortest-path="
      ++ show Search.graphAStarShortestPathRegression)
  putStrLn
    ("graph-astar-deferred-lower-bound="
      ++ show Search.graphAStarDeferredPriorityLowerBoundRegression)
  putStrLn
    ("graph-astar-deferred-matches-eager="
      ++ show Search.graphAStarDeferredMatchesEagerRegression)
  putStrLn
    ("learner-dependency-closure="
      ++ show Search.learnerLogicalGraphRegression)
  putStrLn
    ("learner-semantic-bridge-closure="
      ++ show Search.learnerSemanticBridgeRegression)
  putStrLn
    ("graph-linear-chain="
      ++ show Search.autonomousGraphSearchRegression)
  putStrLn
    ("canonical-search-egraph-closed="
      ++ show Search.canonicalSearchPlanEGraphClosed)
  putStrLn
    ("graph-astar-egraph-closed="
      ++ show Search.graphAStarPlanEGraphClosed)
  putStrLn
    ("graph-search-contract="
      ++ show graphSearchContractPassed)

{-# COMPILE AGDA2HS graphSearchContractPassed #-}
{-# COMPILE AGDA2HS main #-}
