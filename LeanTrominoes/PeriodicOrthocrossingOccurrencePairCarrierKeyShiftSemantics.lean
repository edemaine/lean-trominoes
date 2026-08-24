/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairCarrierKeyData

/-! # Graph-free semantics of one retained carrier-key shift block -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Projecting a computed crossing after one retention shift erases its point
and gives the graph-free occurrence-pair key block. -/
theorem retainedCrossingCarrierKeyShiftBlock_candidate_eq_occurrencePair
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (pair : (IndexedGridSegment × Cell) ×
      (IndexedGridSegment × Cell))
    (shift : Cell) :
    retainedCrossingCarrierKeyShiftBlock graph
        (orientedCrossingCandidate graph pair.1 pair.2) shift =
      occurrencePairCarrierKeyShiftBlock pair shift := by
  simp [retainedCrossingCarrierKeyShiftBlock,
    occurrencePairCarrierKeyShiftBlock,
    orientedCrossingCandidate, CrossingRecord.periodTranslate]

end LeanTrominoes.PeriodicOrthocrossing
