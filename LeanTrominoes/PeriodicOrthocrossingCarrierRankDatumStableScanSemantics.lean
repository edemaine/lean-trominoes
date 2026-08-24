/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.IndexedConsecutivePairsMapSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumStableEnumerationSemantics
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairRetainedCarrierBitData

/-! # Unconditional physical semantics of stable datum scans -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- The stable datum-only adjacent-pair scan of projected physical nodes is
the exact representative carrier bit block, including coordinate ties. -/
theorem retainedCarrierRankDatumBits_map_eq_complete
    (period : Nat) (nodes : List CarrierNode)
    (key : Nat × Nat × Cell) :
    retainedCarrierRankDatumBits
        (nodes.map (carrierNodeRankDatumAtPeriod period)) key =
      retainedRepresentativeCarrierPairBitsAtPeriod
        period nodes key := by
  unfold retainedCarrierRankDatumBits
    retainedRepresentativeCarrierPairBitsAtPeriod
    retainedRepresentativeCarrierNodePairsAtPeriod
    retainedCompleteCarrierNodePairsAtPeriod
  rw [retainedCarrierRankDatumsByLowerRank_map_eq_complete]
  rw [IndexedConsecutivePairs.pairs_map]
  rw [IndexedConsecutivePairs.pairs_eq_consecutivePairs]
  simp only [List.filter_map, List.map_map, Function.comp_def,
    carrierNodeRankDatumAtPeriod_sameCrossoverSite,
    carrierNodeRankDatumAtPeriod_pairIsRepresentative,
    carrierNodeRankDatumAtPeriod_pairBits]

end LeanTrominoes.PeriodicOrthocrossing
