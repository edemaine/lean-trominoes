/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListDedupMapInjectiveOn
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumScanData
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairCarrierNodeRankData

/-! # Carrier rank-datum candidates projected from physical nodes -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- When both the physical and projected presentations are duplicate-free,
datum deduplication and key filtering are exactly the map of the corresponding
physical carrier-node candidates. -/
theorem retainedCarrierRankDatumCandidates_map_eq
    (period : Nat) (nodes : List CarrierNode)
    (key : Nat × Nat × Cell)
    (nodesNodup : nodes.Nodup)
    (datumsNodup :
      (nodes.map (carrierNodeRankDatumAtPeriod period)).Nodup) :
    retainedCarrierRankDatumCandidates
        (nodes.map (carrierNodeRankDatumAtPeriod period)) key =
      (retainedCarrierNodeCandidatesAtPeriod nodes key).map
        (carrierNodeRankDatumAtPeriod period) := by
  unfold retainedCarrierRankDatumCandidates
    retainedCarrierNodeCandidatesAtPeriod
  rw [List.dedup_eq_self.mpr datumsNodup,
    List.dedup_eq_self.mpr nodesNodup, List.filter_map]
  rfl

/-- The natural finite-list condition is injectivity of the datum projection
on presented nodes; this alone makes datum deduplication and key filtering
commute with physical-node projection. -/
theorem retainedCarrierRankDatumCandidates_map_eq_of_injectiveOn
    (period : Nat) (nodes : List CarrierNode)
    (key : Nat × Nat × Cell)
    (injectiveOn : ∀ first ∈ nodes, ∀ second ∈ nodes,
      carrierNodeRankDatumAtPeriod period first =
        carrierNodeRankDatumAtPeriod period second → first = second) :
    retainedCarrierRankDatumCandidates
        (nodes.map (carrierNodeRankDatumAtPeriod period)) key =
      (retainedCarrierNodeCandidatesAtPeriod nodes key).map
        (carrierNodeRankDatumAtPeriod period) := by
  unfold retainedCarrierRankDatumCandidates
    retainedCarrierNodeCandidatesAtPeriod
  rw [List.dedup_map_of_injective_on
    (carrierNodeRankDatumAtPeriod period) nodes injectiveOn,
    List.filter_map]
  rfl

end LeanTrominoes.PeriodicOrthocrossing
