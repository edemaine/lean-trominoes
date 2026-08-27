/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumStableEnumerationSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankGlobalBlockPairSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedRetainedPairMembershipSemantics

/-! # Physical semantics of selected global carrier-rank pairs -/

namespace LeanTrominoes.PeriodicOrthocrossing

namespace CarrierRankGlobal

private theorem retainedCarrierRankDatumsByLowerRank_dedup
    (datums : List CarrierNodeRankDatum) (key : Nat × Nat × Cell) :
    retainedCarrierRankDatumsByLowerRank datums.dedup key =
      retainedCarrierRankDatumsByLowerRank datums key := by
  unfold retainedCarrierRankDatumsByLowerRank
    retainedCarrierRankDatumCandidates
  rw [List.dedup_idem]

/-- Stable key-block datum pairs projected from physical nodes are exactly
the pointwise projections of the physical adjacent carrier-node pairs. -/
theorem dedupKeyBlockDatumPairs_eq_physicalPairs
    (period : Nat) (nodes : List CarrierNode)
    (key : Nat × Nat × Cell) :
    keyBlockDatumPairs
        ((nodes.map (carrierNodeRankDatumAtPeriod period)).dedup) key =
      (IndexedConsecutivePairs.pairs
        (retainedCompleteCarrierNodesAtPeriod period nodes key)).map
          (fun pair =>
            (carrierNodeRankDatumAtPeriod period pair.1,
              carrierNodeRankDatumAtPeriod period pair.2)) := by
  rw [keyBlockDatumPairs_eq _
    (List.nodup_dedup
      (nodes.map (carrierNodeRankDatumAtPeriod period))) key]
  rw [retainedCarrierRankDatumsByLowerRank_dedup]
  rw [retainedCarrierRankDatumsByLowerRank_map_eq_complete]
  exact IndexedConsecutivePairs.pairs_map
    (retainedCompleteCarrierNodesAtPeriod period nodes key)
    (carrierNodeRankDatumAtPeriod period)

end CarrierRankGlobal

namespace CarrierRankOrderedPairs

/-- Every selected numeric matrix entry has unique physical endpoints forming
an adjacent pair in the reconstructed retained carrier chain. -/
theorem retainedPredicate_exists_physicalPair
    (period : Nat) (nodes : List CarrierNode)
    (first second : (CarrierNodeRankDatum × Nat) × Nat)
    (firstMember : first ∈
      (CarrierRankGlobal.enumeration
        ((nodes.map (carrierNodeRankDatumAtPeriod period)).dedup)).zipIdx)
    (secondMember : second ∈
      (CarrierRankGlobal.enumeration
        ((nodes.map (carrierNodeRankDatumAtPeriod period)).dedup)).zipIdx)
    (retained : retainedPredicate first second = true) :
    ∃ pair : CarrierNode × CarrierNode,
      pair ∈ IndexedConsecutivePairs.pairs
        (retainedCompleteCarrierNodesAtPeriod
          period nodes first.1.1.key) ∧
      carrierNodeRankDatumAtPeriod period pair.1 = first.1.1 ∧
      carrierNodeRankDatumAtPeriod period pair.2 = second.1.1 := by
  let datums :=
    (nodes.map (carrierNodeRankDatumAtPeriod period)).dedup
  have selected := retainedPredicate_keyBlockDatumPair datums
    first second firstMember secondMember retained
  have mappedMember : (first.1.1, second.1.1) ∈
      (IndexedConsecutivePairs.pairs
        (retainedCompleteCarrierNodesAtPeriod
          period nodes first.1.1.key)).map
            (fun pair =>
              (carrierNodeRankDatumAtPeriod period pair.1,
                carrierNodeRankDatumAtPeriod period pair.2)) := by
    rw [← CarrierRankGlobal.dedupKeyBlockDatumPairs_eq_physicalPairs]
    exact selected.1
  rcases List.mem_map.mp mappedMember with
    ⟨pair, pairMember, pairEq⟩
  exact ⟨pair, pairMember, congrArg Prod.fst pairEq,
    congrArg Prod.snd pairEq⟩

end CarrierRankOrderedPairs
end LeanTrominoes.PeriodicOrthocrossing
