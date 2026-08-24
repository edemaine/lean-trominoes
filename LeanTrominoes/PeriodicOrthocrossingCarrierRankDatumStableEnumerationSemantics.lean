/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeRankDatumSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumCandidateSemantics
import LeanTrominoes.StableListRankEnumerationSemantics

/-! # Unconditional physical semantics of stable datum ranks -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Stable datum ranks commute with physical-node projection and recover the
exact deduplicated stable carrier sort, including coordinate ties. -/
theorem retainedCarrierRankDatumsByLowerRank_map_eq_complete
    (period : Nat) (nodes : List CarrierNode)
    (key : Nat × Nat × Cell) :
    retainedCarrierRankDatumsByLowerRank
        (nodes.map (carrierNodeRankDatumAtPeriod period)) key =
      (retainedCompleteCarrierNodesAtPeriod period nodes key).map
        (carrierNodeRankDatumAtPeriod period) := by
  let project := carrierNodeRankDatumAtPeriod period
  let candidates := retainedCarrierNodeCandidatesAtPeriod nodes key
  have candidateEq :=
    retainedCarrierRankDatumCandidates_map_eq_of_injectiveOn
      period nodes key fun first firstMember second secondMember equal =>
        carrierNodeRankDatumAtPeriod_injective period equal
  have mappedSort := List.map_insertionSort
    (r := fun first second : CarrierNode =>
      carrierNodeOrderCoordinateAtPeriod period first ≤
        carrierNodeOrderCoordinateAtPeriod period second)
    (s := fun first second : CarrierNodeRankDatum =>
      first.orderCoordinate ≤ second.orderCoordinate)
    project candidates (by
      intro first firstMember second secondMember
      rfl)
  unfold retainedCarrierRankDatumsByLowerRank
  rw [candidateEq]
  rw [StableListRanks.valuesByStableLowerRank_eq_insertionSort]
  simpa [project, candidates, retainedCarrierNodeCandidatesAtPeriod,
    retainedCompleteCarrierNodesAtPeriod] using mappedSort.symm

end LeanTrominoes.PeriodicOrthocrossing
