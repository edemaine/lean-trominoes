/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GroupedConsecutivePairsSemantics
import LeanTrominoes.IndexedConsecutivePairsMatrixSemantics
import LeanTrominoes.ListZipIdxFstMembership
import LeanTrominoes.PeriodicOrthocrossingCarrierRankGlobalBlockPairData
import LeanTrominoes.PeriodicOrthocrossingCarrierRankGlobalBlockSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedRetainedPairMaskNumericSemantics

/-! # Global block semantics of rank-ordered retained carrier pairs -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankOrderedPairs

private theorem filterMap_two_predicates
    {Value Output : Type*} (values : List Value)
    (first second : Value → Bool) (output : Value → Output) :
    values.filterMap (fun value =>
        if first value && second value then some (output value) else none) =
      ((values.filter first).filter second).map output := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      cases firstActive : first value <;>
        cases secondActive : second value <;>
          simp only [List.filterMap_cons, List.filter_cons, List.map_cons,
            firstActive, secondActive, Bool.false_and, Bool.true_and,
            Bool.false_eq_true, ↓reduceIte]
      all_goals rw [induction]

private theorem enumeration_eq_semanticKeyBlocks
    (datums : List CarrierNodeRankDatum) :
    CarrierRankGlobal.enumeration datums =
      (datums.map CarrierNodeRankDatum.key).dedup.flatMap fun key =>
        CarrierRankGlobal.keyBlock datums
          (CarrierRankCompiledKey.ofKey key) := by
  unfold CarrierRankGlobal.enumeration
  rw [show datums.map CarrierRankCompiledKey.ofDatum =
      (datums.map CarrierNodeRankDatum.key).map
        CarrierRankCompiledKey.ofKey by
    simp [List.map_map, CarrierRankCompiledKey.ofDatum]]
  rw [List.dedup_map_of_injective
    CarrierRankCompiledKey.ofKey_injective]
  rw [List.flatMap_map]

private theorem keyBlock_nonempty
    (datums : List CarrierNodeRankDatum)
    (key : Nat × Nat × Cell)
    (keyMember : key ∈
      (datums.map CarrierNodeRankDatum.key).dedup) :
    CarrierRankGlobal.keyBlock datums
        (CarrierRankCompiledKey.ofKey key) ≠ [] := by
  have presentedKeyMember : key ∈
      datums.map CarrierNodeRankDatum.key :=
    List.mem_dedup.mp keyMember
  rcases List.mem_map.mp presentedKeyMember with
    ⟨datum, datumMember, datumKeyEq⟩
  rcases exists_mem_zipIdx_fst datums 0 datumMember with
    ⟨index, indexedMember⟩
  have blockMember : (datum, index) ∈
      CarrierRankGlobal.keyBlock datums
        (CarrierRankCompiledKey.ofKey key) :=
    (CarrierRankGlobal.mem_keyBlock_iff datums
      (CarrierRankCompiledKey.ofKey key) (datum, index)).mpr
      ⟨indexedMember, by
        unfold CarrierRankGlobal.entryKey CarrierRankGlobal.datumKey
        simp [CarrierRankCompiledKey.ofDatum, datumKeyEq]⟩
  intro blockNil
  rw [blockNil] at blockMember
  exact List.not_mem_nil blockMember

private theorem keyBlock_entry_key
    (datums : List CarrierNodeRankDatum)
    (key : Nat × Nat × Cell)
    (entry : CarrierNodeRankDatum × Nat)
    (entryMember : entry ∈
      CarrierRankGlobal.keyBlock datums
        (CarrierRankCompiledKey.ofKey key)) :
    entry.1.key = key := by
  have compiledEq := CarrierRankGlobal.entryKey_eq_of_mem_keyBlock
    datums (CarrierRankCompiledKey.ofKey key) entry entryMember
  simpa [CarrierRankGlobal.entryKey, CarrierRankGlobal.datumKey,
    CarrierRankCompiledKey.ofDatum] using compiledEq

private theorem keyBlock_filterMap_eq_bits
    (datums : List CarrierNodeRankDatum)
    (key : Nat × Nat × Cell) :
    (IndexedConsecutivePairs.pairs
        (CarrierRankGlobal.keyBlock datums
          (CarrierRankCompiledKey.ofKey key))).filterMap (fun pair =>
      if !pair.1.1.sameCrossoverSite pair.2.1 &&
          pair.1.1.pairIsRepresentative pair.2.1 then
        some (pair.1.1.pairBits pair.2.1)
      else none) =
      CarrierRankGlobal.keyBlockBits datums key := by
  unfold CarrierRankGlobal.keyBlockBits
    CarrierRankGlobal.keyBlockDatumPairs
  rw [List.filter_map, List.filter_map, List.map_map]
  exact filterMap_two_predicates
    (IndexedConsecutivePairs.pairs
      (CarrierRankGlobal.keyBlock datums
        (CarrierRankCompiledKey.ofKey key)))
    (fun pair : (CarrierNodeRankDatum × Nat) ×
        (CarrierNodeRankDatum × Nat) =>
      !pair.1.1.sameCrossoverSite pair.2.1)
    (fun pair : (CarrierNodeRankDatum × Nat) ×
        (CarrierNodeRankDatum × Nat) =>
      pair.1.1.pairIsRepresentative pair.2.1)
    (fun pair : (CarrierNodeRankDatum × Nat) ×
        (CarrierNodeRankDatum × Nat) =>
      pair.1.1.pairBits pair.2.1)

private theorem keyBlock_filterMap_eq_mappedPairs
    (datums : List CarrierNodeRankDatum)
    (key : Nat × Nat × Cell)
    (word : CarrierNodeRankDatum → List Bool) :
    (IndexedConsecutivePairs.pairs
        (CarrierRankGlobal.keyBlock datums
          (CarrierRankCompiledKey.ofKey key))).filterMap (fun pair =>
      if !pair.1.1.sameCrossoverSite pair.2.1 &&
          pair.1.1.pairIsRepresentative pair.2.1 then
        some (word pair.1.1, word pair.2.1)
      else none) =
      ((((CarrierRankGlobal.keyBlockDatumPairs datums key).filter fun pair =>
          !pair.1.sameCrossoverSite pair.2).filter fun pair =>
            pair.1.pairIsRepresentative pair.2).map fun pair =>
              (word pair.1, word pair.2)) := by
  unfold CarrierRankGlobal.keyBlockDatumPairs
  rw [List.filter_map, List.filter_map, List.map_map]
  exact filterMap_two_predicates
    (IndexedConsecutivePairs.pairs
      (CarrierRankGlobal.keyBlock datums
        (CarrierRankCompiledKey.ofKey key)))
    (fun pair : (CarrierNodeRankDatum × Nat) ×
        (CarrierNodeRankDatum × Nat) =>
      !pair.1.1.sameCrossoverSite pair.2.1)
    (fun pair : (CarrierNodeRankDatum × Nat) ×
        (CarrierNodeRankDatum × Nat) =>
      pair.1.1.pairIsRepresentative pair.2.1)
    (fun pair : (CarrierNodeRankDatum × Nat) ×
        (CarrierNodeRankDatum × Nat) =>
      (word pair.1.1, word pair.2.1))

/-- The sparse row-major retained-pair target is exactly the concatenation
of the established per-key bit blocks in dedup-last semantic-key order. -/
theorem retainedRowMajorBits_eq_keyBlocks
    (datums : List CarrierNodeRankDatum) :
    let entries := CarrierRankGlobal.enumeration datums
    (entries.zipIdx.flatMap fun first =>
      entries.zipIdx.filterMap fun second =>
        if retainedPredicate first second then
          some
            (first.1.1.horizontal,
              first.1.1.pairNextSlice second.1.1)
        else none) =
      (datums.map CarrierNodeRankDatum.key).dedup.flatMap
        (CarrierRankGlobal.keyBlockBits datums) := by
  let entries := CarrierRankGlobal.enumeration datums
  let selected := fun
      (first second : CarrierNodeRankDatum × Nat) =>
        !first.1.sameCrossoverSite second.1 &&
        first.1.pairIsRepresentative second.1
  let output := fun (first second : CarrierNodeRankDatum × Nat) =>
    first.1.pairBits second.1
  change entries.zipIdx.flatMap (fun first =>
      entries.zipIdx.filterMap fun second =>
        if retainedPredicate first second then
          some (output first.1 second.1)
        else none) = _
  have predicateEq :
      entries.zipIdx.flatMap (fun first =>
          entries.zipIdx.filterMap fun second =>
            if retainedPredicate first second then
              some (output first.1 second.1)
            else none) =
        entries.zipIdx.flatMap (fun first =>
          entries.zipIdx.filterMap fun second =>
            if decide (second.2 = first.2 + 1) &&
                (decide (first.1.1.key = second.1.1.key) &&
                  selected first.1 second.1) then
              some (output first.1 second.1)
            else none) := by
    apply List.flatMap_congr
    intro first _firstMember
    apply List.filterMap_congr
    intro second _secondMember
    simp only [retainedPredicate, selected, Bool.and_assoc,
      Bool.and_left_comm, Bool.and_comm]
  rw [predicateEq]
  have successorEq :=
    IndexedConsecutivePairs.zipIdx_successorMatrix_filterMap entries
      (fun first second =>
        decide (first.1.key = second.1.key) && selected first second)
      output
  rw [successorEq]
  simp only [entries]
  rw [enumeration_eq_semanticKeyBlocks]
  rw [groupedPairs_filterMap
    (datums.map CarrierNodeRankDatum.key).dedup
    (fun key => CarrierRankGlobal.keyBlock datums
      (CarrierRankCompiledKey.ofKey key))
    (fun entry => entry.1.key)
    selected output
    (List.nodup_dedup _)
    (keyBlock_nonempty datums)
    (fun key _keyMember entry entryMember =>
      keyBlock_entry_key datums key entry entryMember)]
  apply List.flatMap_congr
  intro key _keyMember
  exact keyBlock_filterMap_eq_bits datums key

/-- Selecting a row-major global-rank square and projecting both endpoints
is exactly the concatenation of the retained per-key datum-pair blocks. -/
theorem retainedRowMajorMappedPairs_eq_keyBlocks
    (datums : List CarrierNodeRankDatum)
    (word : CarrierNodeRankDatum → List Bool) :
    let entries := CarrierRankGlobal.enumeration datums
    (entries.zipIdx.flatMap fun first =>
      entries.zipIdx.filterMap fun second =>
        if retainedPredicate first second then
          some (word first.1.1, word second.1.1)
        else none) =
      (datums.map CarrierNodeRankDatum.key).dedup.flatMap fun key =>
        ((((CarrierRankGlobal.keyBlockDatumPairs datums key).filter fun pair =>
            !pair.1.sameCrossoverSite pair.2).filter fun pair =>
              pair.1.pairIsRepresentative pair.2).map fun pair =>
                (word pair.1, word pair.2)) := by
  let entries := CarrierRankGlobal.enumeration datums
  let selected := fun
      (first second : CarrierNodeRankDatum × Nat) =>
        !first.1.sameCrossoverSite second.1 &&
        first.1.pairIsRepresentative second.1
  let output := fun (first second : CarrierNodeRankDatum × Nat) =>
    (word first.1, word second.1)
  change entries.zipIdx.flatMap (fun first =>
      entries.zipIdx.filterMap fun second =>
        if retainedPredicate first second then
          some (output first.1 second.1)
        else none) = _
  have predicateEq :
      entries.zipIdx.flatMap (fun first =>
          entries.zipIdx.filterMap fun second =>
            if retainedPredicate first second then
              some (output first.1 second.1)
            else none) =
        entries.zipIdx.flatMap (fun first =>
          entries.zipIdx.filterMap fun second =>
            if decide (second.2 = first.2 + 1) &&
                (decide (first.1.1.key = second.1.1.key) &&
                  selected first.1 second.1) then
              some (output first.1 second.1)
            else none) := by
    apply List.flatMap_congr
    intro first _firstMember
    apply List.filterMap_congr
    intro second _secondMember
    simp only [retainedPredicate, selected, Bool.and_assoc,
      Bool.and_left_comm, Bool.and_comm]
  rw [predicateEq]
  have successorEq :=
    IndexedConsecutivePairs.zipIdx_successorMatrix_filterMap entries
      (fun first second =>
        decide (first.1.key = second.1.key) && selected first second)
      output
  rw [successorEq]
  simp only [entries]
  rw [enumeration_eq_semanticKeyBlocks]
  rw [groupedPairs_filterMap
    (datums.map CarrierNodeRankDatum.key).dedup
    (fun key => CarrierRankGlobal.keyBlock datums
      (CarrierRankCompiledKey.ofKey key))
    (fun entry => entry.1.key)
    selected output
    (List.nodup_dedup _)
    (keyBlock_nonempty datums)
    (fun key _keyMember entry entryMember =>
      keyBlock_entry_key datums key entry entryMember)]
  apply List.flatMap_congr
  intro key _keyMember
  exact keyBlock_filterMap_eq_mappedPairs datums key word

end CarrierRankOrderedPairs
end LeanTrominoes.PeriodicOrthocrossing
