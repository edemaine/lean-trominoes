/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Tromino.Finite.FiniteICompletionDecision

namespace LeanTrominoes.Tromino.FiniteI
open FiniteWitness
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

-- A certificate may protrude beyond the box it covers.
example : Valid Tromino.I (box 0) ∅ {horizontal 0 0} := by decide +kernel
example : Tromino.I.Completable Set.univ (∅ : Set (Finset Cell)) := by
  simpa only [Finset.coe_empty] using
    completion_of_witness (show Valid Tromino.I (box 0) ∅ {horizontal 0 0} by decide +kernel)

-- Malformed preplacements are rejected, rather than silently discarded.
example : decideCompletion {{(0,0)}}=false := by decide +kernel
example : decideCompletion ∅=true := by decide +kernel

end LeanTrominoes.Tromino.FiniteI
