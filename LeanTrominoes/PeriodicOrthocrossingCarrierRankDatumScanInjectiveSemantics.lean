/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeRankDatumBitScanData
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumEnumerationInjectiveSemantics

/-! # Datum-only bit scans from finite-list injectivity -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Finite-list injectivity and strict carrier order identify the datum-only
bit scan with the projected physical-node rank scan. -/
theorem retainedCarrierRankDatumBits_map_eq_of_injectiveOn
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
    retainedCarrierRankDatumBits
        (nodes.map (carrierNodeRankDatumAtPeriod period)) key =
      retainedCarrierRankDatumBitsAtPeriod period nodes key := by
  unfold retainedCarrierRankDatumBits
    retainedCarrierRankDatumBitsAtPeriod
  rw [retainedCarrierRankDatumsByLowerRank_map_eq_of_injectiveOn
    period nodes key injectiveOn ordered]

end LeanTrominoes.PeriodicOrthocrossing
