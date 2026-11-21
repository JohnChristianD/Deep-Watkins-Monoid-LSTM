{-# OPTIONS
--erasure
--experimental-lazy-instances
--lossy-unification
--syntactic-equality=1
--no-eta-equality
--prop
--with-K
--no-fast-reduce
--no-projection-like
--erased-quotients
--erased-funext
--erased-propext
--auto-inline
--exact-split
#-}

------------------------------------------------------------------------
-- Canonical learner semantics.
------------------------------------------------------------------------

module FullCoupled.CanonicalLearnerMonolith where

-- Merged external import surface; internal FullCoupled imports remain module-local.
-- The agda2hs base library provides the Haskell-facing Prelude,
-- including Haskell.Prim's core types, equality, and Double.
-- Numeric/vector kernels use Csimma's postulate + FOREIGN AGDA2HS boundary;
-- the executable result carries an erased S0 simulation witness.
-- This model has a Haskell extraction boundary, but no C/C++ pointer/event
-- boundary: IORef, Ptr, StablePtr, C types, MVar, and CFuture adapters do not
-- belong in its recurrent kernel.
--
open import Haskell.Prelude public

{-# FOREIGN AGDA2HS
{-# LANGUAGE BangPatterns #-}
import qualified Data.Bits as Bits
import Data.Int (Int64)
import Data.Word (Word64)
import Data.Vector.Unboxed (Vector)
import qualified Data.Vector.Unboxed as VU

