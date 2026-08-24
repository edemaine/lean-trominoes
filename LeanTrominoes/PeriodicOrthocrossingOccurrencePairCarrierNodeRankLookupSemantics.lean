/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairCarrierNodeRankLookupData
import LeanTrominoes.StrictListRankLookupSemantics

/-! # Exact sorted-chain semantics of carrier rank lookup -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Direct lower-rank lookup returns the exact node at the corresponding
index of a strictly ordered retained carrier chain. -/
theorem retainedCarrierNodeAtLowerRank?_eq_sorted_getElem?
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
    retainedCarrierNodeAtLowerRank?
      period nodes key index = some node := by
  unfold retainedCarrierNodeAtLowerRank?
    retainedCarrierNodeCandidatesAtPeriod
  exact StrictListRanks.valueAtLowerRank?_eq_sorted_getElem?
    (carrierNodeOrderCoordinateAtPeriod period)
    (nodes.dedup.filter fun candidate => candidate.carrierKey = key)
    (by simpa [retainedCompleteCarrierNodesAtPeriod] using ordered)
    index node
    (by simpa [retainedCompleteCarrierNodesAtPeriod] using lookup)

end LeanTrominoes.PeriodicOrthocrossing
