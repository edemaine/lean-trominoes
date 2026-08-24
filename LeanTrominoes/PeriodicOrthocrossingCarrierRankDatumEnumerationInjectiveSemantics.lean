/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumCandidateSemantics
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairCarrierNodeRankEnumerationData
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumStableEnumerationSemantics
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairCarrierNodeRankEnumerationSemantics

/-! # Datum rank enumeration from finite-list injectivity -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Injectivity of the datum projection on the presented nodes and strict
carrier order suffice to commute datum-only rank enumeration with physical
node projection. -/
theorem retainedCarrierRankDatumsByLowerRank_map_eq_of_injectiveOn
    (period : Nat) (nodes : List CarrierNode)
    (key : Nat × Nat × Cell)
    (_injectiveOn : ∀ first ∈ nodes, ∀ second ∈ nodes,
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
  rw [retainedCarrierRankDatumsByLowerRank_map_eq_complete]
  rw [retainedCarrierNodesByLowerRankAtPeriod_eq
    period nodes key ordered]

end LeanTrominoes.PeriodicOrthocrossing
