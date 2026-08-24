/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeRankDatumBitScanData
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumEnumerationSemantics

/-! # Physical-node semantics of datum-only carrier bit scans -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Under duplicate-freedom and strict carrier order, the complete datum-only
scan of projected physical nodes is exactly the established projected-node
rank bit scan. -/
theorem retainedCarrierRankDatumBits_map_eq
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
      retainedCarrierRankDatumBitsAtPeriod period nodes key := by
  unfold retainedCarrierRankDatumBits
    retainedCarrierRankDatumBitsAtPeriod
  rw [retainedCarrierRankDatumsByLowerRank_map_eq
    period nodes key nodesNodup datumsNodup ordered]

end LeanTrominoes.PeriodicOrthocrossing
