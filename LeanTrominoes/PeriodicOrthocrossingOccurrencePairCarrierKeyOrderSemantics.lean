/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairCarrierKeyOrderData
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierKeyScanSemantics
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairCarrierKeyScanSemantics

/-! # Graph-free semantics of exact retained carrier-key order -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- The selected retained carrier-key list depends only on the ordered
neighbor occurrence stream and its ordered accepted crossing-pair stream. -/
theorem retainedNeighboringCarrierKeys_eq_occurrencesAndPairs
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    retainedNeighboringCarrierKeys graph =
      retainedCarrierKeysOfOccurrencesAndPairs
        (neighborOccurrences graph)
        (orientedCrossingOccurrencePairs graph) := by
  rw [retainedNeighboringCarrierKeys_eq_scan_dedup_filter,
    retainedCrossingCarrierKeyScan_eq_graphFreeOccurrencePairs]
  rfl

end LeanTrominoes.PeriodicOrthocrossing
