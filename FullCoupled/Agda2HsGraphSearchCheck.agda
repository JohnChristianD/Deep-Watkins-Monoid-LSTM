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
    && Search.nodeHeuristicLowerBoundRegression
    && Search.graphCycleIsRejectedRegression
    && Search.autonomousGraphSearchRegression
    && Search.canonicalSearchPlanEGraphClosed

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
    ("graph-admissible-heuristic="
      ++ show Search.nodeHeuristicLowerBoundRegression)
  putStrLn
    ("graph-cycle-rejected="
      ++ show Search.graphCycleIsRejectedRegression)
  putStrLn
    ("graph-linear-chain="
      ++ show Search.autonomousGraphSearchRegression)
  putStrLn
    ("canonical-search-egraph-closed="
      ++ show Search.canonicalSearchPlanEGraphClosed)
  putStrLn
    ("graph-search-contract="
      ++ show graphSearchContractPassed)

{-# COMPILE AGDA2HS graphSearchContractPassed #-}
{-# COMPILE AGDA2HS main #-}
