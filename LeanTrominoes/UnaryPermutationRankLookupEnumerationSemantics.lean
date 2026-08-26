/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListMapIdxOfSelfBEq
import LeanTrominoes.ListRangeGetD
import LeanTrominoes.PaddedSupportedLastRepresentativeLookupSemantics
import LeanTrominoes.UnaryPermutationRankLookupSemantics

/-! # Unary permutation lookup enumerates mapped entries -/

namespace LeanTrominoes
namespace UnaryPermutationRankLookup

private theorem getD_map_idxOf_of_mem
    {Entry Output : Type*} [DecidableEq Entry]
    (entries : List Entry) (output : Entry → Output) (default : Output)
    {entry : Entry} (member : entry ∈ entries) :
    (entries.map output).getD
        (@List.idxOf Entry instBEqOfDecidableEq entry entries) default =
      output entry := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_idxOf member]
  rfl

/-- Looking up a mapped presentation stream by each entry's exact index in
a duplicate-free permutation emits the mapped permutation itself. -/
theorem values_map_idxOf_of_perm
    {Entry : Type*} [DecidableEq Entry]
    (presented ordered : List Entry)
    (permutation : ordered.Perm presented)
    (orderedNodup : ordered.Nodup)
    (datum : Entry → Nat) :
    values
        (presented.map fun entry =>
          @List.idxOf Entry instBEqOfDecidableEq entry ordered)
        (presented.map datum) =
      ordered.map datum := by
  letI : BEq Entry := instBEqOfDecidableEq
  let ranks := presented.map fun entry => ordered.idxOf entry
  let orderedData := ordered.map datum
  have ranksPermutation :
      ranks.Perm (List.range ranks.length) := by
    have mapped := permutation.map fun entry => ordered.idxOf entry
    rw [List.map_idxOf_self_eq_range_beq ordered orderedNodup] at mapped
    simpa [ranks, permutation.length_eq] using mapped.symm
  have presentedDataEq :
      presented.map datum =
        ranks.map fun rank => orderedData.getD rank 0 := by
    unfold ranks
    rw [List.map_map]
    apply List.map_congr_left
    intro entry entryMember
    symm
    exact getD_map_idxOf_of_mem ordered datum 0
      (permutation.mem_iff.mpr entryMember)
  change values ranks (presented.map datum) = orderedData
  rw [values_eq_orderedValues ranks (presented.map datum)
    (by simp [ranks]) ranksPermutation]
  unfold orderedValues
  rw [presentedDataEq]
  calc
    (List.range ranks.length).map (fun rank =>
        LastTrueUnaryValueLookupMachine.lookup
          (LastRepresentativeEqualityRows.equalityRow ranks rank)
          (ranks.map fun selected => orderedData.getD selected 0)) =
        (List.range ranks.length).map fun rank =>
          orderedData.getD rank 0 := by
      apply List.map_congr_left
      intro rank rankMember
      have rankInRanks : rank ∈ ranks :=
        ranksPermutation.mem_iff.mpr rankMember
      simpa [LastRepresentativeEqualityRows.equalityRow,
        StableOccurrenceRanks.equalityRow] using
        LastTrueUnaryValueLookupMachine.lookup_equalityRow_map
          (fun selected => orderedData.getD selected 0)
          ranks rank rankInRanks
    _ = orderedData := by
      simpa [ranks, orderedData, permutation.length_eq] using
        List.map_range_getD orderedData 0

end UnaryPermutationRankLookup
end LeanTrominoes
