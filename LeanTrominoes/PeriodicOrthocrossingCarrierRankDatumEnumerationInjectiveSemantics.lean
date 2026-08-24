/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumCandidateSemantics
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairCarrierNodeRankEnumerationData
import LeanTrominoes.StrictListRankEnumerationSemantics

/-! # Datum rank enumeration from finite-list injectivity -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Injectivity of the datum projection on the presented nodes and strict
carrier order suffice to commute datum-only rank enumeration with physical
node projection. -/
theorem retainedCarrierRankDatumsByLowerRank_map_eq_of_injectiveOn
    (period : Nat) (nodes : List CarrierNode)
    (key : Nat × Nat × Cell)
    (injectiveOn : ∀ first ∈ nodes, ∀ second ∈ nodes,
      carrierNodeRankDatumAtPeriod period first =
        carrierNodeRankDatumAtPeriod period second → first = second)
    (ordered :
      (retainedCompleteCarrierNodesAtPeriod period nodes key).Pairwise
        fun first second =>
          carrierNodeOrderCoordinateAtPeriod period first <
            carrierNodeOrderCoordinateAtPeriod period second) :
    retainedCarrierRankDatumsByLowerRank
        (nodes.map (carrierNodeRankDatumAtPeriod period)) key =
      (retainedCarrierNodesByLowerRankAtPeriod period nodes key).map
        (carrierNodeRankDatumAtPeriod period) := by
  let project := carrierNodeRankDatumAtPeriod period
  let candidates := retainedCarrierNodeCandidatesAtPeriod nodes key
  have candidateEq :=
    retainedCarrierRankDatumCandidates_map_eq_of_injectiveOn
      period nodes key injectiveOn
  have nodeOrdered :
      (candidates.insertionSort fun first second =>
        carrierNodeOrderCoordinateAtPeriod period first ≤
          carrierNodeOrderCoordinateAtPeriod period second).Pairwise
        fun first second =>
          carrierNodeOrderCoordinateAtPeriod period first <
            carrierNodeOrderCoordinateAtPeriod period second := by
    simpa [candidates, retainedCarrierNodeCandidatesAtPeriod,
      retainedCompleteCarrierNodesAtPeriod] using ordered
  have mappedSort := List.map_insertionSort
    (r := fun first second : CarrierNode =>
      carrierNodeOrderCoordinateAtPeriod period first ≤
        carrierNodeOrderCoordinateAtPeriod period second)
    (s := fun first second : CarrierNodeRankDatum =>
      first.orderCoordinate ≤ second.orderCoordinate)
    project candidates (by
      intro first firstMember second secondMember
      rfl)
  have datumOrdered :
      ((candidates.map project).insertionSort fun first second =>
        first.orderCoordinate ≤ second.orderCoordinate).Pairwise
        fun first second =>
          first.orderCoordinate < second.orderCoordinate := by
    rw [← mappedSort, List.pairwise_map]
    exact nodeOrdered
  unfold retainedCarrierRankDatumsByLowerRank
    retainedCarrierNodesByLowerRankAtPeriod
  rw [candidateEq]
  rw [StrictListRanks.valuesByLowerRank_eq_insertionSort
    _ _ datumOrdered]
  rw [StrictListRanks.valuesByLowerRank_eq_insertionSort
    _ _ nodeOrdered]
  exact mappedSort.symm

end LeanTrominoes.PeriodicOrthocrossing
