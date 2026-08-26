/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordsFirstTrueSemantics
import LeanTrominoes.UnaryPermutationRankLookupData

/-! # Semantics of unary lookup under permutation ranks -/

namespace LeanTrominoes
namespace UnaryPermutationRankLookup

private theorem lookupAux_replicate_false
    (candidate count : Nat) (values : List Nat) :
    LastTrueUnaryValueLookupMachine.lookupAux candidate
        (List.replicate count false) values = candidate := by
  induction count generalizing values with
  | zero => rfl
  | succ count induction =>
      cases values with
      | nil =>
          simpa [List.replicate_succ,
            LastTrueUnaryValueLookupMachine.lookupAux] using
            induction ([] : List Nat)
      | cons value values =>
          simpa [List.replicate_succ,
            LastTrueUnaryValueLookupMachine.lookupAux] using
            induction values

private theorem lookupAux_append_false_suffix
    (candidate : Nat) (row : List Bool) (fieldValues suffix : List Nat)
    (aligned : row.length = fieldValues.length) :
    LastTrueUnaryValueLookupMachine.lookupAux candidate
        (row ++ List.replicate suffix.length false)
        (fieldValues ++ suffix) =
      LastTrueUnaryValueLookupMachine.lookupAux candidate row fieldValues := by
  induction row generalizing candidate fieldValues with
  | nil =>
      have fieldsNil : fieldValues = [] :=
        List.eq_nil_of_length_eq_zero aligned.symm
      subst fieldValues
      simpa [LastTrueUnaryValueLookupMachine.lookupAux] using
        lookupAux_replicate_false candidate suffix.length suffix
  | cons bit row induction =>
      cases fieldValues with
      | nil => simp at aligned
      | cons field fieldValues =>
          have tailAligned : row.length = fieldValues.length := by
            simpa using aligned
          cases bit with
          | false =>
              simpa [LastTrueUnaryValueLookupMachine.lookupAux] using
                induction candidate fieldValues tailAligned
          | true =>
              simpa [LastTrueUnaryValueLookupMachine.lookupAux] using
                induction field fieldValues tailAligned

theorem lookup_append_false_suffix
    (row : List Bool) (fieldValues suffix : List Nat)
    (aligned : row.length = fieldValues.length) :
    LastTrueUnaryValueLookupMachine.lookup
        (row ++ List.replicate suffix.length false)
        (fieldValues ++ suffix) =
      LastTrueUnaryValueLookupMachine.lookup row fieldValues := by
  exact lookupAux_append_false_suffix 0 row fieldValues suffix aligned

private theorem dedup_append_eq_right
    {Value : Type*} [DecidableEq Value]
    (before suffix : List Value)
    (subset : ∀ value ∈ before, value ∈ suffix)
    (suffixNodup : suffix.Nodup) :
    (before ++ suffix).dedup = suffix := by
  induction before with
  | nil =>
      simpa using List.dedup_eq_self.mpr suffixNodup
  | cons value tail induction =>
      have valueMember : value ∈ tail ++ suffix :=
        List.mem_append_right tail (subset value (by simp))
      rw [List.cons_append, List.dedup_cons_of_mem valueMember]
      exact induction
        (fun other otherMember => subset other (by simp [otherMember]))

/-- Appending the canonical range forces last-occurrence deduplication into
increasing rank order. -/
theorem extendedRanks_dedup_eq_range (ranks : List Nat)
    (permutation : List.Perm ranks (List.range ranks.length)) :
    (extendedRanks ranks).dedup = List.range ranks.length := by
  unfold extendedRanks UnaryFieldRange.values
  apply dedup_append_eq_right
  · intro rank rankMember
    exact permutation.mem_iff.mp rankMember
  · exact List.nodup_range

/-- Semantic lookup values indexed by the canonical increasing rank list. -/
def orderedValues (ranks fieldValues : List Nat) : List Nat :=
  (List.range ranks.length).map fun rank =>
    LastTrueUnaryValueLookupMachine.lookup
      (LastRepresentativeEqualityRows.equalityRow ranks rank) fieldValues

/-- If the ranks are a permutation of `0, ..., n - 1`, the compiled lookup
emits exactly the aligned field selected by each increasing rank. -/
theorem values_eq_orderedValues (ranks fieldValues : List Nat)
    (aligned : fieldValues.length = ranks.length)
    (permutation : List.Perm ranks (List.range ranks.length)) :
    values ranks fieldValues = orderedValues ranks fieldValues := by
  have ranksNodup : ranks.Nodup :=
    permutation.nodup_iff.mpr List.nodup_range
  unfold values rankRows orderedValues
    LastTrueUnaryValueLookupMachine.lookups
  rw [extendedRanks_dedup_eq_range ranks permutation]
  simp only [List.map_map]
  apply List.map_congr_left
  intro rank rankMember
  have rankInRanks : rank ∈ ranks := permutation.mem_iff.mpr rankMember
  simp only [Function.comp_apply]
  unfold extendedRanks
  rw [DelimitedBinaryWordsFirstTrue.row_equalityRow_append_of_nodup_mem
    ranks (UnaryFieldRange.values ranks) rank ranksNodup rankInRanks]
  simpa [paddedValues, UnaryFieldRange.values,
    UnaryFieldConstantStreams.zeros] using
    lookup_append_false_suffix
      (LastRepresentativeEqualityRows.equalityRow ranks rank)
      fieldValues (UnaryFieldConstantStreams.zeros ranks)
      (by simp [LastRepresentativeEqualityRows.equalityRow, aligned])

end UnaryPermutationRankLookup
end LeanTrominoes
