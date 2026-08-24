/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairRetainedCarrierKeyScanData
import LeanTrominoes.PeriodicOrthocrossingRetainedCrossingCarrierKeyScanSemantics
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingPairOrder

/-! # Exact occurrence-pair semantics of retained crossing carrier keys -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- The retained crossing-key stream is exactly the accepted occurrence-pair
scan, with each pair expanded to its fixed retention-shift block. -/
theorem retainedCrossingCarrierKeyScan_eq_occurrencePairs
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    retainedCrossingCarrierKeyScan graph =
      occurrencePairRetainedCarrierKeyScan graph := by
  unfold retainedCrossingCarrierKeyScan
    occurrencePairRetainedCarrierKeyScan
    occurrencePairRetainedCarrierKeyBlock
  rw [orientedCrossings_eq_orientedCrossingPairFilter,
    orientedCrossingPairFilter_eq_map_occurrencePairs,
    List.flatMap_map]

end LeanTrominoes.PeriodicOrthocrossing
