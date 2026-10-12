{-# OPTIONS
  --erasure
  --no-projection-like
#-}

module FullCoupled.Agda2HsGraphSearchCheck where

-- BEGIN MIRTH-SYNC CANONICAL COMMAND
-- "$AGDA_COMMAND" -i .
-- END MIRTH-SYNC CANONICAL COMMAND

open import Haskell.Prelude
import FullCoupled.Agda2HsSemanticSearch as Search

-- This checker imports only the Agda2HS runtime modules. It does not import
-- TheoremsMonolith or any TypeTopology module.
graphSearchContractPassed : Bool
graphSearchContractPassed =
  Search.graphDependencyOrderRegression
    && Search.graphTwoLeafBranchesRegression
    && Search.graphAStarTieBreakRegression
    && Search.graphCycleIsMaximalRegression
    && Search.autonomousGraphSearchRegression

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
    ("graph-cycle-policy="
      ++ show Search.graphCycleIsMaximalRegression)
  putStrLn
    ("graph-linear-chain="
      ++ show Search.autonomousGraphSearchRegression)
  putStrLn
    ("graph-search-contract="
      ++ show graphSearchContractPassed)

{-# COMPILE AGDA2HS graphSearchContractPassed #-}
{-# COMPILE AGDA2HS main #-}
