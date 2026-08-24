/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairCarrierKeyShiftSemantics

/-! # Graph-free semantics of one retained occurrence-pair key block -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- The complete retention-shift expansion of a computed crossing is exactly
the graph-free occurrence-pair carrier-key block. -/
theorem occurrencePairRetainedCarrierKeyBlock_eq_graphFree
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (pair : (IndexedGridSegment × Cell) ×
      (IndexedGridSegment × Cell)) :
    occurrencePairRetainedCarrierKeyBlock graph pair =
      occurrencePairCarrierKeyBlock pair := by
  unfold occurrencePairRetainedCarrierKeyBlock
    retainedCrossingCarrierKeyBlock occurrencePairCarrierKeyBlock
  apply List.flatMap_congr
  intro shift _shiftMember
  exact
    retainedCrossingCarrierKeyShiftBlock_candidate_eq_occurrencePair
      graph pair shift

end LeanTrominoes.PeriodicOrthocrossing
