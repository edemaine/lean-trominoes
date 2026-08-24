/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairCarrierKeyBlockSemantics
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairRetainedCarrierKeyScanSemantics

/-! # Graph-free semantics of the retained crossing key scan -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- The retained crossing-key scan is the graph-free fixed-block expansion
of the accepted neighboring occurrence-pair stream. -/
theorem retainedCrossingCarrierKeyScan_eq_graphFreeOccurrencePairs
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    retainedCrossingCarrierKeyScan graph =
      occurrencePairCarrierKeyScan
        (orientedCrossingOccurrencePairs graph) := by
  rw [retainedCrossingCarrierKeyScan_eq_occurrencePairs]
  unfold occurrencePairRetainedCarrierKeyScan
    occurrencePairCarrierKeyScan
  apply List.flatMap_congr
  intro pair _pairMember
  exact occurrencePairRetainedCarrierKeyBlock_eq_graphFree graph pair

end LeanTrominoes.PeriodicOrthocrossing
