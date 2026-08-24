/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairCarrierNodeRankData

/-! # Sorted-index semantics of graph-free carrier-node ranks -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Lower-coordinate counting in the unsorted retained-node presentation
recovers the exact index in the established strictly ordered carrier chain. -/
theorem retainedCarrierNodeLowerRankAtPeriod_eq_index
    (period : Nat) (nodes : List CarrierNode)
    (key : Nat × Nat × Cell)
    (ordered :
      (retainedCompleteCarrierNodesAtPeriod period nodes key).Pairwise
        fun first second =>
          carrierNodeOrderCoordinateAtPeriod period first <
            carrierNodeOrderCoordinateAtPeriod period second)
    (index : Nat) (node : CarrierNode)
    (lookup :
      (retainedCompleteCarrierNodesAtPeriod
        period nodes key)[index]? = some node) :
    retainedCarrierNodeLowerRankAtPeriod
      period nodes key node = index := by
  unfold retainedCarrierNodeLowerRankAtPeriod
    retainedCarrierNodeCandidatesAtPeriod
  exact StrictListRanks.lowerRank_eq_sortedIndex_of_getElem?
    (carrierNodeOrderCoordinateAtPeriod period)
    (nodes.dedup.filter fun candidate => candidate.carrierKey = key)
    (by simpa [retainedCompleteCarrierNodesAtPeriod] using ordered)
    index node
    (by simpa [retainedCompleteCarrierNodesAtPeriod] using lookup)

end LeanTrominoes.PeriodicOrthocrossing
