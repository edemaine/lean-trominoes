/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.IndexedConsecutivePairsSemantics
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairCarrierNodeRankEnumerationData
import LeanTrominoes.StrictListRankEnumerationSemantics

/-! # Exact carrier-chain semantics of rank-major reconstruction -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Rank-major enumeration reproduces the exact retained carrier-node sort. -/
theorem retainedCarrierNodesByLowerRankAtPeriod_eq
    (period : Nat) (nodes : List CarrierNode)
    (key : Nat × Nat × Cell)
    (ordered :
      (retainedCompleteCarrierNodesAtPeriod period nodes key).Pairwise
        fun first second =>
          carrierNodeOrderCoordinateAtPeriod period first <
            carrierNodeOrderCoordinateAtPeriod period second) :
    retainedCarrierNodesByLowerRankAtPeriod period nodes key =
      retainedCompleteCarrierNodesAtPeriod period nodes key := by
  unfold retainedCarrierNodesByLowerRankAtPeriod
    retainedCarrierNodeCandidatesAtPeriod
    retainedCompleteCarrierNodesAtPeriod
  exact StrictListRanks.valuesByLowerRank_eq_insertionSort
    (carrierNodeOrderCoordinateAtPeriod period)
    (nodes.dedup.filter fun candidate => candidate.carrierKey = key)
    ordered

/-- Indexed adjacency and crossover suppression over the rank-major stream
reproduce the exact retained complete-carrier endpoint pairs. -/
theorem retainedCarrierNodePairsByLowerRankAtPeriod_eq
    (period : Nat) (nodes : List CarrierNode)
    (key : Nat × Nat × Cell)
    (ordered :
      (retainedCompleteCarrierNodesAtPeriod period nodes key).Pairwise
        fun first second =>
          carrierNodeOrderCoordinateAtPeriod period first <
            carrierNodeOrderCoordinateAtPeriod period second) :
    retainedCarrierNodePairsByLowerRankAtPeriod period nodes key =
      retainedCompleteCarrierNodePairsAtPeriod period nodes key := by
  unfold retainedCarrierNodePairsByLowerRankAtPeriod
    retainedCompleteCarrierNodePairsAtPeriod
  rw [IndexedConsecutivePairs.pairs_eq_consecutivePairs,
    retainedCarrierNodesByLowerRankAtPeriod_eq period nodes key ordered]

end LeanTrominoes.PeriodicOrthocrossing
