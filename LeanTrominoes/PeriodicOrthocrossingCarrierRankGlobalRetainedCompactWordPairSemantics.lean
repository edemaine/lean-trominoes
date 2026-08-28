/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeCodeSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedRetainedPairPhysicalSemantics
import LeanTrominoes.PeriodicOrthocrossingGuardedCarrierSourcePairCompactAtomWordData
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairRetainedCarrierRepresentativeData

/-! # Physical semantics of retained compact carrier-word pairs -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankGlobal

/-- Filtering one deduplicated global-rank key block and projecting its
reversible datum identities yields exactly the compact words of the
representative physical carrier-node pairs. -/
theorem dedupKeyBlockRetainedCompactWordPairs_eq_physicalPairs
    (period : Nat) (nodes : List CarrierNode)
    (key : Nat × Nat × Cell) :
    let datums :=
      (nodes.map (carrierNodeRankDatumAtPeriod period)).dedup
    ((((keyBlockDatumPairs datums key).filter fun pair =>
        !pair.1.sameCrossoverSite pair.2).filter fun pair =>
          pair.1.pairIsRepresentative pair.2).map fun pair =>
            (CarrierNodeNormalizedSourceKeys.compactWordAtPeriod
                period pair.1.identity.node,
              CarrierNodeNormalizedSourceKeys.compactWordAtPeriod
                period pair.2.identity.node)) =
      (retainedRepresentativeCarrierNodePairsAtPeriod
        period nodes key).map fun pair =>
          (CarrierNodeNormalizedSourceKeys.compactWordAtPeriod
              period pair.1,
            CarrierNodeNormalizedSourceKeys.compactWordAtPeriod
              period pair.2) := by
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
  simp [carrierNodeRankDatumAtPeriod]

/-- Concatenating the retained compact-word identity over every deduplicated
stable key block gives the corresponding physical representative-pair
blocks with no change of key order. -/
theorem dedupGlobalRetainedCompactWordPairs_eq_physicalPairs
    (period : Nat) (nodes : List CarrierNode) :
    let datums :=
      (nodes.map (carrierNodeRankDatumAtPeriod period)).dedup
    let keys := (datums.map CarrierNodeRankDatum.key).dedup
    keys.flatMap (fun key =>
      ((((keyBlockDatumPairs datums key).filter fun pair =>
          !pair.1.sameCrossoverSite pair.2).filter fun pair =>
            pair.1.pairIsRepresentative pair.2).map fun pair =>
              (CarrierNodeNormalizedSourceKeys.compactWordAtPeriod
                  period pair.1.identity.node,
                CarrierNodeNormalizedSourceKeys.compactWordAtPeriod
                  period pair.2.identity.node))) =
      keys.flatMap fun key =>
        (retainedRepresentativeCarrierNodePairsAtPeriod
          period nodes key).map fun pair =>
            (CarrierNodeNormalizedSourceKeys.compactWordAtPeriod
                period pair.1,
              CarrierNodeNormalizedSourceKeys.compactWordAtPeriod
                period pair.2) := by
  dsimp only
  apply List.flatMap_congr
  intro key _keyMember
  exact dedupKeyBlockRetainedCompactWordPairs_eq_physicalPairs
    period nodes key

end CarrierRankGlobal
end LeanTrominoes.PeriodicOrthocrossing
