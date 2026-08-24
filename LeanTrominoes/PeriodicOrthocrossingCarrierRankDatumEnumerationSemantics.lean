/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumCandidateSemantics
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairCarrierNodeRankEnumerationData
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumStableEnumerationSemantics
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairCarrierNodeRankEnumerationSemantics

/-! # Physical-node semantics of datum-only rank enumeration -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Under duplicate-freedom and strict carrier order, datum-only lower-rank
enumeration is exactly the pointwise projection of physical-node lower-rank
enumeration. -/
theorem retainedCarrierRankDatumsByLowerRank_map_eq
    (period : Nat) (nodes : List CarrierNode)
    (key : Nat × Nat × Cell)
    (_nodesNodup : nodes.Nodup)
    (_datumsNodup :
      (nodes.map (carrierNodeRankDatumAtPeriod period)).Nodup)
    (ordered :
      (retainedCompleteCarrierNodesAtPeriod period nodes key).Pairwise
        fun first second =>
          carrierNodeOrderCoordinateAtPeriod period first <
            carrierNodeOrderCoordinateAtPeriod period second) :
    retainedCarrierRankDatumsByLowerRank
        (nodes.map (carrierNodeRankDatumAtPeriod period)) key =
      (retainedCarrierNodesByLowerRankAtPeriod period nodes key).map
        (carrierNodeRankDatumAtPeriod period) := by
  rw [retainedCarrierRankDatumsByLowerRank_map_eq_complete]
  rw [retainedCarrierNodesByLowerRankAtPeriod_eq
    period nodes key ordered]

end LeanTrominoes.PeriodicOrthocrossing
