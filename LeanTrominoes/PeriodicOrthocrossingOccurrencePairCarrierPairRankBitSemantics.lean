/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairCarrierNodeRankEnumerationSemantics
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairCarrierPairRankBitData

/-! # Exact semantics of rank-major representative carrier bits -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Representative filtering of the rank-major pairs preserves the exact
established representative endpoint order. -/
theorem retainedRepresentativeCarrierNodePairsByLowerRankAtPeriod_eq
    (period : Nat) (nodes : List CarrierNode)
    (key : Nat × Nat × Cell)
    (ordered :
      (retainedCompleteCarrierNodesAtPeriod period nodes key).Pairwise
        fun first second =>
          carrierNodeOrderCoordinateAtPeriod period first <
            carrierNodeOrderCoordinateAtPeriod period second) :
    retainedRepresentativeCarrierNodePairsByLowerRankAtPeriod
        period nodes key =
      retainedRepresentativeCarrierNodePairsAtPeriod
        period nodes key := by
  unfold retainedRepresentativeCarrierNodePairsByLowerRankAtPeriod
    retainedRepresentativeCarrierNodePairsAtPeriod
  rw [retainedCarrierNodePairsByLowerRankAtPeriod_eq
    period nodes key ordered]

/-- Rank-major reconstruction emits the exact established axis and
next-slice bit block for one retained carrier key. -/
theorem retainedRepresentativeCarrierPairBitsByLowerRankAtPeriod_eq
    (period : Nat) (nodes : List CarrierNode)
    (key : Nat × Nat × Cell)
    (ordered :
      (retainedCompleteCarrierNodesAtPeriod period nodes key).Pairwise
        fun first second =>
          carrierNodeOrderCoordinateAtPeriod period first <
            carrierNodeOrderCoordinateAtPeriod period second) :
    retainedRepresentativeCarrierPairBitsByLowerRankAtPeriod
        period nodes key =
      retainedRepresentativeCarrierPairBitsAtPeriod
        period nodes key := by
  unfold retainedRepresentativeCarrierPairBitsByLowerRankAtPeriod
    retainedRepresentativeCarrierPairBitsAtPeriod
  rw [retainedRepresentativeCarrierNodePairsByLowerRankAtPeriod_eq
    period nodes key ordered]

end LeanTrominoes.PeriodicOrthocrossing
