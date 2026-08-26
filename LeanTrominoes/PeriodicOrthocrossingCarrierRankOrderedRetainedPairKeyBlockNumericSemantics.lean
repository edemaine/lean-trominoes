/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankGlobalBlockPairSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedRetainedPairGlobalSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedRetainedPairNumericSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierRankDatumStableSemantics

/-! # Per-key semantics of compiled rank-ordered retained pairs -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankOrderedPairs

private theorem retainedCarrierRankDatumBits_dedup
    (datums : List CarrierNodeRankDatum)
    (key : Nat × Nat × Cell) :
    retainedCarrierRankDatumBits datums.dedup key =
      retainedCarrierRankDatumBits datums key := by
  unfold retainedCarrierRankDatumBits
    retainedCarrierRankDatumsByLowerRank
    retainedCarrierRankDatumCandidates
  rw [List.dedup_idem]

/-- Each global block reconstructed from deduplicated route data is exactly
the established route-descriptor representative-link bit block. -/
theorem dedupKeyBlockBits_eq_routeDescriptorBits
    (period : Nat) (descriptors : List RouteDescriptor)
    (key : Nat × Nat × Cell) :
    let sourceDatums :=
      routeDescriptorCarrierRankDatumsAtPeriod period descriptors
    let datums := sourceDatums.dedup
    CarrierRankGlobal.keyBlockBits datums key =
      routeDescriptorRetainedCarrierPairBitsAtPeriod
        period descriptors key := by
  let sourceDatums :=
    routeDescriptorCarrierRankDatumsAtPeriod period descriptors
  let datums := sourceDatums.dedup
  change CarrierRankGlobal.keyBlockBits datums key = _
  rw [CarrierRankGlobal.keyBlockBits_eq_retainedCarrierRankDatumBits
    datums (List.nodup_dedup sourceDatums) key]
  rw [retainedCarrierRankDatumBits_dedup sourceDatums key]
  exact
    routeDescriptorRetainedCarrierPairBitsByRankDatumAtPeriod_eq_unconditionally
      period descriptors key

/-- On valid numeric routes, the sparse compiler output is the concatenation
of exact route-descriptor pair blocks in the datum stream's dedup-last key
order. -/
theorem retainedPairBits_numericRouteDescriptors_eq_keyBlocks
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    retainedPairBits (PeriodicCNF.numericRouteDescriptors formula) =
      let descriptors := PeriodicCNF.numericRouteDescriptors formula
      let period := routeDescriptorStreamGridSize descriptors
      let sourceDatums :=
        routeDescriptorCarrierRankDatumsAtPeriod period descriptors
      let datums := sourceDatums.dedup
      (datums.map CarrierNodeRankDatum.key).dedup.flatMap fun key =>
        routeDescriptorRetainedCarrierPairBitsAtPeriod
          period descriptors key := by
  let descriptors := PeriodicCNF.numericRouteDescriptors formula
  let period := routeDescriptorStreamGridSize descriptors
  let sourceDatums :=
    routeDescriptorCarrierRankDatumsAtPeriod period descriptors
  let datums := sourceDatums.dedup
  rw [retainedPairBits_numericRouteDescriptors
    formula wellFormed degree isLocal forward nonempty]
  change (let entries := CarrierRankGlobal.enumeration datums
    entries.zipIdx.flatMap fun first =>
      entries.zipIdx.filterMap fun second =>
        if retainedPredicate first second then
          some
            (first.1.1.horizontal,
              first.1.1.pairNextSlice second.1.1)
        else none) = _
  rw [retainedRowMajorBits_eq_keyBlocks datums]
  apply List.flatMap_congr
  intro key _keyMember
  exact dedupKeyBlockBits_eq_routeDescriptorBits period descriptors key

end CarrierRankOrderedPairs
end LeanTrominoes.PeriodicOrthocrossing
