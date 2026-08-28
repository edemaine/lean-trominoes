/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordFixedFieldLookupSemantics
import LeanTrominoes.ListMapIdxOfSelfBEq
import LeanTrominoes.ListRangeGetD
import LeanTrominoes.UnaryPermutationRankBlockLookupData
import LeanTrominoes.UnaryPermutationRankLookupEnumerationSemantics

/-! # Semantics of fixed-width permutation-rank block lookup -/

namespace LeanTrominoes
namespace UnaryPermutationRankBlockLookup

open LastTrueUnaryValueLookupMachine

private theorem flatMap_eq_flatten_map
    {Source Target : Type*} (items : List Source)
    (blocks : Source → List Target) :
    items.flatMap blocks = (items.map blocks).flatten := by
  induction items with
  | nil => rfl
  | cons item items induction =>
      simp only [List.flatMap_cons, List.map_cons, List.flatten_cons,
        induction]

private theorem zeros_flatMap
    {Source : Type*} (items : List Source) (fields : Source → List Nat) :
    UnaryFieldConstantStreams.zeros (items.flatMap fields) =
      items.flatMap fun item =>
        UnaryFieldConstantStreams.zeros (fields item) := by
  unfold UnaryFieldConstantStreams.zeros
  rw [List.map_flatMap]

private theorem paddedValues_flatMap_eq_blocks
    {Source : Type*} (items : List Source) (fields : Source → List Nat) :
    paddedValues (items.flatMap fields) =
      (items.map fields ++ items.map (fun item =>
        UnaryFieldConstantStreams.zeros (fields item))).flatten := by
  unfold paddedValues
  rw [List.flatten_append, ← flatMap_eq_flatten_map,
    ← flatMap_eq_flatten_map, ← zeros_flatMap]

private theorem blocksAligned
    {Source : Type*} (width : Nat) (fields : Source → List Nat)
    (bits : List Bool) (items : List Source)
    (fieldLength : ∀ item ∈ items, (fields item).length = width)
    (lengthEq : bits.length = items.length) :
    List.Forall₂ (fun _ block => block.length = width)
      bits (items.map fields) := by
  induction bits generalizing items with
  | nil =>
      have itemsEq : items = [] :=
        List.eq_nil_of_length_eq_zero lengthEq.symm
      subst items
      exact List.Forall₂.nil
  | cons bit bits induction =>
      cases items with
      | nil => simp at lengthEq
      | cons item items =>
          have tailLength : bits.length = items.length := by
            simpa using lengthEq
          exact List.Forall₂.cons (fieldLength item (by simp))
            (induction items
              (fun other otherMember => fieldLength other (by
                simp [otherMember]))
              tailLength)

private theorem idxOf_eq_iff_of_mem
    {Entry : Type*} [DecidableEq Entry]
    (entries : List Entry) {first second : Entry}
    (firstMember : first ∈ entries) (secondMember : second ∈ entries) :
    @List.idxOf Entry instBEqOfDecidableEq first entries =
        @List.idxOf Entry instBEqOfDecidableEq second entries ↔
      first = second := by
  constructor
  · intro equal
    have firstLookup := List.getElem?_idxOf firstMember
    have secondLookup := List.getElem?_idxOf secondMember
    rw [equal, secondLookup] at firstLookup
    exact Option.some.inj firstLookup.symm
  · intro equal
    exact congrArg
      (fun entry => @List.idxOf Entry instBEqOfDecidableEq entry entries)
      equal

private theorem equalityRow_map_idxOf
    {Entry : Type*} [DecidableEq Entry]
    (presented ordered : List Entry) (target : Entry)
    (presentedSubset : ∀ entry ∈ presented, entry ∈ ordered)
    (targetMember : target ∈ ordered) :
    LastRepresentativeEqualityRows.equalityRow
        (presented.map fun entry =>
          @List.idxOf Entry instBEqOfDecidableEq entry ordered)
        (@List.idxOf Entry instBEqOfDecidableEq target ordered) =
      LastRepresentativeEqualityRows.equalityRow presented target := by
  unfold LastRepresentativeEqualityRows.equalityRow
  rw [List.map_map]
  apply List.map_congr_left
  intro entry entryMember
  simp only [Function.comp_apply]
  have entryMemberOrdered := presentedSubset entry entryMember
  by_cases same : target = entry
  · subst entry
    simp
  · have indicesNe :
        @List.idxOf Entry instBEqOfDecidableEq target ordered ≠
          @List.idxOf Entry instBEqOfDecidableEq entry ordered := by
      intro indicesEqual
      exact same ((idxOf_eq_iff_of_mem ordered targetMember
        entryMemberOrdered).mp indicesEqual)
    simp [same, indicesNe]

private theorem rankRows_eq_orderedRows
    {Entry : Type*} [DecidableEq Entry]
    (presented ordered : List Entry)
    (permutation : ordered.Perm presented)
    (orderedNodup : ordered.Nodup) :
    UnaryPermutationRankLookup.rankRows
        (presented.map fun entry =>
          @List.idxOf Entry instBEqOfDecidableEq entry ordered) =
      ⟨ordered.map fun entry =>
        DelimitedBinaryWordsFirstTrue.row
          (LastRepresentativeEqualityRows.equalityRow
            (UnaryPermutationRankLookup.extendedRanks
              (presented.map fun item =>
                @List.idxOf Entry instBEqOfDecidableEq item ordered))
            (@List.idxOf Entry instBEqOfDecidableEq entry ordered))⟩ := by
  letI : BEq Entry := instBEqOfDecidableEq
  let ranks := presented.map fun entry => ordered.idxOf entry
  have ranksPermutation :
      ranks.Perm (List.range ranks.length) := by
    have mapped := permutation.map fun entry => ordered.idxOf entry
    rw [List.map_idxOf_self_eq_range_beq ordered orderedNodup] at mapped
    simpa [ranks, permutation.length_eq] using mapped.symm
  unfold UnaryPermutationRankLookup.rankRows
  rw [UnaryPermutationRankLookup.extendedRanks_dedup_eq_range
    ranks ranksPermutation]
  have orderedRange :=
    List.map_idxOf_self_eq_range_beq ordered orderedNodup
  have rankLength : ranks.length = ordered.length := by
    simp [ranks, permutation.length_eq]
  rw [rankLength, ← orderedRange, List.map_map]
  rfl

private theorem lookup_expanded_rankRow
    {Entry : Type*} [DecidableEq Entry]
    (presented ordered : List Entry)
    (permutation : ordered.Perm presented)
    (orderedNodup : ordered.Nodup)
    (fields : Entry → List Nat) (width index : Nat)
    (fieldLength : ∀ entry, (fields entry).length = width)
    (indexLt : index < width) (target : Entry)
    (targetMember : target ∈ ordered) :
    lookup
        (DelimitedBinaryWordFixedFieldRowExpansion.row width index
          (DelimitedBinaryWordsFirstTrue.row
            (LastRepresentativeEqualityRows.equalityRow
              (UnaryPermutationRankLookup.extendedRanks
                (presented.map fun entry =>
                  @List.idxOf Entry instBEqOfDecidableEq entry ordered))
              (@List.idxOf Entry instBEqOfDecidableEq target ordered))))
        (paddedValues (presented.flatMap fields)) =
      (fields target).getD index 0 := by
  letI : BEq Entry := instBEqOfDecidableEq
  let ranks := presented.map fun entry => ordered.idxOf entry
  let zeroFields : Entry → List Nat := fun entry =>
    UnaryFieldConstantStreams.zeros (fields entry)
  let blocks := presented.map fields ++ presented.map zeroFields
  have presentedSubset : ∀ entry ∈ presented, entry ∈ ordered := by
    intro entry entryMember
    exact permutation.mem_iff.mpr entryMember
  have targetPresented : target ∈ presented :=
    permutation.mem_iff.mp targetMember
  have rankMember : ordered.idxOf target ∈ ranks := by
    exact List.mem_map.mpr ⟨target, targetPresented, rfl⟩
  have ranksPermutation : ranks.Perm (List.range ranks.length) := by
    have mapped := permutation.map fun entry => ordered.idxOf entry
    rw [List.map_idxOf_self_eq_range_beq ordered orderedNodup] at mapped
    simpa [ranks, permutation.length_eq] using mapped.symm
  have ranksNodup : ranks.Nodup :=
    ranksPermutation.nodup_iff.mpr List.nodup_range
  have firstTrueEq :
      DelimitedBinaryWordsFirstTrue.row
          (LastRepresentativeEqualityRows.equalityRow
            (UnaryPermutationRankLookup.extendedRanks ranks)
            (ordered.idxOf target)) =
        LastRepresentativeEqualityRows.equalityRow ranks
            (ordered.idxOf target) ++
          List.replicate (UnaryFieldRange.values ranks).length false := by
    unfold UnaryPermutationRankLookup.extendedRanks
    exact DelimitedBinaryWordsFirstTrue.row_equalityRow_append_of_nodup_mem
      ranks (UnaryFieldRange.values ranks) (ordered.idxOf target)
      ranksNodup rankMember
  have blockLengths : ∀ block ∈ blocks, block.length = width := by
    intro block blockMember
    rcases List.mem_append.mp blockMember with blockMember | blockMember
    · rcases List.mem_map.mp blockMember with ⟨entry, _member, rfl⟩
      exact fieldLength entry
    · rcases List.mem_map.mp blockMember with ⟨entry, _member, rfl⟩
      simp [zeroFields, UnaryFieldConstantStreams.zeros,
        fieldLength entry]
  have rowLength :
      (DelimitedBinaryWordsFirstTrue.row
        (LastRepresentativeEqualityRows.equalityRow
          (UnaryPermutationRankLookup.extendedRanks ranks)
          (ordered.idxOf target))).length = blocks.length := by
    simp [blocks, UnaryPermutationRankLookup.extendedRanks,
      UnaryFieldRange.values, ranks]
  have alignedBlocks :
      List.Forall₂ (fun _ block => block.length = width)
        (DelimitedBinaryWordsFirstTrue.row
          (LastRepresentativeEqualityRows.equalityRow
            (UnaryPermutationRankLookup.extendedRanks ranks)
            (ordered.idxOf target))) blocks := by
    simpa using blocksAligned width id
      (DelimitedBinaryWordsFirstTrue.row
        (LastRepresentativeEqualityRows.equalityRow
          (UnaryPermutationRankLookup.extendedRanks ranks)
          (ordered.idxOf target))) blocks blockLengths rowLength
  rw [paddedValues_flatMap_eq_blocks]
  rw [DelimitedBinaryWordFixedFieldRowExpansion.lookup_row_flatten
    width index _ blocks indexLt (by simpa [ranks] using alignedBlocks)]
  rw [firstTrueEq]
  have rankLength : ranks.length = presented.length := by
    simp [ranks]
  have originalColumnLength :
      (LastRepresentativeEqualityRows.equalityRow ranks
        (ordered.idxOf target)).length =
        (presented.map fun entry => (fields entry).getD index 0).length := by
    simp [LastRepresentativeEqualityRows.equalityRow, rankLength]
  rw [List.map_append, List.map_map, List.map_map]
  change lookup
      (LastRepresentativeEqualityRows.equalityRow ranks
          (ordered.idxOf target) ++
        List.replicate (UnaryFieldRange.values ranks).length false)
      ((presented.map fun entry => (fields entry).getD index 0) ++
        (presented.map fun entry => (zeroFields entry).getD index 0)) =
    (fields target).getD index 0
  have suffixLength :
      (UnaryFieldRange.values ranks).length =
        (presented.map fun entry =>
          (zeroFields entry).getD index 0).length := by
    simp [UnaryFieldRange.values, ranks]
  rw [suffixLength]
  rw [UnaryPermutationRankLookup.lookup_append_false_suffix
    (LastRepresentativeEqualityRows.equalityRow ranks
      (ordered.idxOf target))
    (presented.map fun entry => (fields entry).getD index 0)
    (presented.map fun entry => (zeroFields entry).getD index 0)
    originalColumnLength]
  rw [equalityRow_map_idxOf presented ordered target
    presentedSubset targetMember]
  exact lookup_equalityRow_map
    (fun entry => (fields entry).getD index 0)
    presented target targetPresented

/-- Looking up fixed-width blocks by permutation ranks emits the blocks in
the duplicate-free reference order. -/
theorem values_flatMap_idxOf_of_perm
    {Entry : Type*} [DecidableEq Entry]
    (presented ordered : List Entry)
    (permutation : ordered.Perm presented)
    (orderedNodup : ordered.Nodup)
    (fields : Entry → List Nat) (width : Nat)
    (fieldLength : ∀ entry, (fields entry).length = width) :
    values width
        (presented.map fun entry =>
          @List.idxOf Entry instBEqOfDecidableEq entry ordered)
        (presented.flatMap fields) =
      ordered.flatMap fields := by
  unfold values expandedRows
    DelimitedBinaryWordFixedFieldRowExpansion.rows
    LastTrueUnaryValueLookupMachine.lookups
  rw [rankRows_eq_orderedRows presented ordered permutation orderedNodup]
  simp only [List.map_flatMap, List.flatMap_map, List.map_map]
  apply List.flatMap_congr
  intro target targetMember
  calc
    (List.range width).map (fun index =>
        lookup
          (DelimitedBinaryWordFixedFieldRowExpansion.row width index
            (DelimitedBinaryWordsFirstTrue.row
              (LastRepresentativeEqualityRows.equalityRow
                (UnaryPermutationRankLookup.extendedRanks
                  (presented.map fun entry =>
                    @List.idxOf Entry instBEqOfDecidableEq entry ordered))
                (@List.idxOf Entry instBEqOfDecidableEq target ordered))))
          (paddedValues (presented.flatMap fields))) =
      (List.range width).map fun index =>
        (fields target).getD index 0 := by
          apply List.map_congr_left
          intro index indexMember
          exact lookup_expanded_rankRow presented ordered permutation
            orderedNodup fields width index fieldLength
            (List.mem_range.mp indexMember) target targetMember
    _ = fields target := by
      simpa [fieldLength target] using
        List.map_range_getD (fields target) 0

end UnaryPermutationRankBlockLookup
end LeanTrominoes
