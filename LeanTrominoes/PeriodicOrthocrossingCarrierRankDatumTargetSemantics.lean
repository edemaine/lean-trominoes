/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeRankDatumBitScanSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumScanSemantics
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairCarrierPairRankBitSemantics

/-! # Exact target semantics of datum-only carrier scans -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Under the three explicit stream invariants, the datum-only rank scan
emits the exact established representative carrier bit block. -/
theorem retainedCarrierRankDatumBits_map_eq_target
    (period : Nat) (nodes : List CarrierNode)
    (key : Nat × Nat × Cell)
    (nodesNodup : nodes.Nodup)
    (datumsNodup :
      (nodes.map (carrierNodeRankDatumAtPeriod period)).Nodup)
    (ordered :
      (retainedCompleteCarrierNodesAtPeriod period nodes key).Pairwise
        fun first second =>
          carrierNodeOrderCoordinateAtPeriod period first <
            carrierNodeOrderCoordinateAtPeriod period second) :
    retainedCarrierRankDatumBits
        (nodes.map (carrierNodeRankDatumAtPeriod period)) key =
      retainedRepresentativeCarrierPairBitsAtPeriod
        period nodes key := by
  rw [retainedCarrierRankDatumBits_map_eq
    period nodes key nodesNodup datumsNodup ordered]
  rw [retainedCarrierRankDatumBitsAtPeriod_eq]
  exact retainedRepresentativeCarrierPairBitsByLowerRankAtPeriod_eq
    period nodes key ordered

end LeanTrominoes.PeriodicOrthocrossing
