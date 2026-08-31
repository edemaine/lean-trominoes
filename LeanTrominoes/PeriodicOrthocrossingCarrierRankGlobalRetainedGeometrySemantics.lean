/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierFallbackRouteTailRecordGeometryData
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeRankDatumSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedRetainedPairPhysicalSemantics

/-! # Physical meaning of retained compiler geometries -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankGlobal

open CarrierFallbackRouteTailRecords

/-- Filtering one deduplicated rank block and projecting its finite geometry
is the same projection of its representative physical node pairs. -/
theorem dedupKeyBlockRetainedGeometries_eq_physicalPairs
    (period : Nat) (nodes : List CarrierNode)
    (key : Nat × Nat × Cell) :
    let datums :=
      (nodes.map (carrierNodeRankDatumAtPeriod period)).dedup
    ((((keyBlockDatumPairs datums key).filter fun pair =>
        !pair.1.sameCrossoverSite pair.2).filter fun pair =>
          pair.1.pairIsRepresentative pair.2).map fun pair =>
            Geometry.ofRankDatums pair.1 pair.2) =
      (retainedRepresentativeCarrierNodePairsAtPeriod
        period nodes key).map (Geometry.ofNodePairAtPeriod period) := by
  dsimp only
  rw [dedupKeyBlockDatumPairs_eq_physicalPairs period nodes key]
  unfold retainedRepresentativeCarrierNodePairsAtPeriod
    retainedCompleteCarrierNodePairsAtPeriod
  rw [IndexedConsecutivePairs.pairs_eq_consecutivePairs]
  simp only [List.filter_map, List.map_map, Function.comp_def,
    carrierNodeRankDatumAtPeriod_sameCrossoverSite,
    carrierNodeRankDatumAtPeriod_pairIsRepresentative]
  apply List.map_congr_left
  intro pair _pairMember
  rfl

/-- The preceding equality concatenates over every stable carrier key
without changing presentation order. -/
theorem dedupGlobalRetainedGeometries_eq_physicalPairs
    (period : Nat) (nodes : List CarrierNode) :
    let datums :=
      (nodes.map (carrierNodeRankDatumAtPeriod period)).dedup
    let keys := (datums.map CarrierNodeRankDatum.key).dedup
    keys.flatMap (fun key =>
      ((((keyBlockDatumPairs datums key).filter fun pair =>
          !pair.1.sameCrossoverSite pair.2).filter fun pair =>
            pair.1.pairIsRepresentative pair.2).map fun pair =>
              Geometry.ofRankDatums pair.1 pair.2)) =
      keys.flatMap fun key =>
        (retainedRepresentativeCarrierNodePairsAtPeriod
          period nodes key).map (Geometry.ofNodePairAtPeriod period) := by
  dsimp only
  apply List.flatMap_congr
  intro key _keyMember
  exact dedupKeyBlockRetainedGeometries_eq_physicalPairs
    period nodes key

end CarrierRankGlobal
end LeanTrominoes.PeriodicOrthocrossing
