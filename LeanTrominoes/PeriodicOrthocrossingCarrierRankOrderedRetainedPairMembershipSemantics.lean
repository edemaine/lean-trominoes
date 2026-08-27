/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.IndexedListScan
import LeanTrominoes.PeriodicOrthocrossingCarrierRankGlobalBlockPairData
import LeanTrominoes.PeriodicOrthocrossingCarrierRankGlobalSameKeySuccessorSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedRetainedPairMaskNumericSemantics

/-! # Membership semantics of selected global carrier-rank pairs -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankOrderedPairs

/-- A selected row-major matrix entry is an adjacent pair in the stable
block for its semantic carrier key, together with the two retained-link
filters recorded by the predicate. -/
theorem retainedPredicate_keyBlockDatumPair
    (datums : List CarrierNodeRankDatum)
    (first second : (CarrierNodeRankDatum × Nat) × Nat)
    (firstMember : first ∈ (CarrierRankGlobal.enumeration datums).zipIdx)
    (secondMember : second ∈ (CarrierRankGlobal.enumeration datums).zipIdx)
    (retained : retainedPredicate first second = true) :
    (first.1.1, second.1.1) ∈
        CarrierRankGlobal.keyBlockDatumPairs datums first.1.1.key ∧
      (!first.1.1.sameCrossoverSite second.1.1) = true ∧
      first.1.1.pairIsRepresentative second.1.1 = true := by
  simp only [retainedPredicate, Bool.and_eq_true] at retained
  have keyEqual : first.1.1.key = second.1.1.key :=
    of_decide_eq_true retained.1.1.1
  have successor : second.2 = first.2 + 1 :=
    of_decide_eq_true retained.1.1.2
  have firstEnumerationMember :
      first.1 ∈ CarrierRankGlobal.enumeration datums :=
    List.fst_mem_of_mem_zipIdx firstMember
  have secondEnumerationMember :
      second.1 ∈ CarrierRankGlobal.enumeration datums :=
    List.fst_mem_of_mem_zipIdx secondMember
  have firstPresented : first.1 ∈ datums.zipIdx :=
    (CarrierRankGlobal.mem_enumeration_iff datums first.1).mp
      firstEnumerationMember
  have secondPresented : second.1 ∈ datums.zipIdx :=
    (CarrierRankGlobal.mem_enumeration_iff datums second.1).mp
      secondEnumerationMember
  have firstIndex :=
    IndexedListScan.idxOf_fst_eq_snd_of_mem_zipIdx
      (CarrierRankGlobal.enumeration datums)
      (CarrierRankGlobal.enumeration_nodup datums) first firstMember
  have secondIndex :=
    IndexedListScan.idxOf_fst_eq_snd_of_mem_zipIdx
      (CarrierRankGlobal.enumeration datums)
      (CarrierRankGlobal.enumeration_nodup datums) second secondMember
  have rankSuccessor :
      CarrierRankGlobal.rankAt datums second.1 =
        CarrierRankGlobal.rankAt datums first.1 + 1 := by
    rw [CarrierRankGlobal.rankAt_eq_idxOf_enumeration
        datums second.1 secondPresented,
      CarrierRankGlobal.rankAt_eq_idxOf_enumeration
        datums first.1 firstPresented,
      secondIndex, firstIndex, successor]
  have sameCompiledKey :
      CarrierRankGlobal.entryKey first.1 =
        CarrierRankGlobal.entryKey second.1 := by
    unfold CarrierRankGlobal.entryKey CarrierRankGlobal.datumKey
    simp [CarrierRankCompiledKey.ofDatum, keyEqual]
  have blockPair :=
    (CarrierRankGlobal.rankAt_eq_succ_iff_mem_keyBlock_pairs
      datums first.1 second.1 firstPresented secondPresented
      sameCompiledKey).mp rankSuccessor
  have firstEntryKey :
      CarrierRankGlobal.entryKey first.1 =
        CarrierRankCompiledKey.ofKey first.1.1.key := by
    rfl
  rw [firstEntryKey] at blockPair
  refine ⟨List.mem_map.mpr ⟨(first.1, second.1), blockPair, rfl⟩,
    retained.1.2, retained.2⟩

end CarrierRankOrderedPairs
end LeanTrominoes.PeriodicOrthocrossing
