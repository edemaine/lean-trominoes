/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.IndexedConsecutivePairsMapSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeRankDatumBitScanData
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeRankDatumSemantics

/-! # Exact semantics of carrier rank-datum bit scans -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- The compiler-facing numeric datum scan emits exactly the representative
rank-major carrier-pair bit block. -/
theorem retainedCarrierRankDatumBitsAtPeriod_eq
    (period : Nat) (nodes : List CarrierNode)
    (key : Nat × Nat × Cell) :
    retainedCarrierRankDatumBitsAtPeriod period nodes key =
      retainedRepresentativeCarrierPairBitsByLowerRankAtPeriod
        period nodes key := by
  unfold retainedCarrierRankDatumBitsAtPeriod
    retainedRepresentativeCarrierPairBitsByLowerRankAtPeriod
    retainedRepresentativeCarrierNodePairsByLowerRankAtPeriod
    retainedCarrierNodePairsByLowerRankAtPeriod
  dsimp only
  rw [IndexedConsecutivePairs.pairs_map]
  simp only [List.filter_map, List.map_map, Function.comp_def,
    carrierNodeRankDatumAtPeriod_sameCrossoverSite,
    carrierNodeRankDatumAtPeriod_pairIsRepresentative,
    carrierNodeRankDatumAtPeriod_pairBits]

end LeanTrominoes.PeriodicOrthocrossing
