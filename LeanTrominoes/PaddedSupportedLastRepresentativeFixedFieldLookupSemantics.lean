/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordFixedFieldLookupSemantics
import LeanTrominoes.ListOptionSupportedDedup
import LeanTrominoes.ListRangeGetD
import LeanTrominoes.PaddedSupportedCandidateSelfSupport
import LeanTrominoes.PaddedSupportedLastRepresentativeLookupSentinelSemantics

/-! # Fixed-field lookup through padded last representatives -/

namespace LeanTrominoes
namespace PaddedSupportedLastRepresentativeEqualityRows

open LastTrueUnaryValueLookupMachine

variable {Value : Type*} [DecidableEq Value]

omit [DecidableEq Value] in
private theorem blocksAligned
    (width : Nat) (fields : Option Value → List Nat)
    (fieldLength : ∀ value, (fields value).length = width)
    (bits : List Bool) (values : List (Option Value))
    (lengthEq : bits.length = values.length) :
    List.Forall₂ (fun _ block => block.length = width)
      bits (values.map fields) := by
  induction bits generalizing values with
  | nil =>
      have valuesEq : values = [] :=
        List.eq_nil_of_length_eq_zero lengthEq.symm
      subst values
      exact List.Forall₂.nil
  | cons bit bits induction =>
      cases values with
      | nil => simp at lengthEq
      | cons value values =>
          have tailLength : bits.length = values.length := by
            simpa using lengthEq
          exact List.Forall₂.cons (fieldLength value)
            (induction values tailLength)

private theorem lookup_expanded_supportedRow
    (base : List Value) (candidates : List (Candidate Value))
    (fields : Option Value → List Nat) (width index : Nat)
    (fieldLength : ∀ value, (fields value).length = width)
    (indexLt : index < width) (target : Option Value)
    (targetMem : target ∈ values candidates)
    (supported : target ∈ base.map some) :
    lookup
        (DelimitedBinaryWordFixedFieldRowExpansion.row width index
          (SupportedLastRepresentativeEqualityRows.row
            (base.map some) (values candidates) target))
        ((values candidates ++ [none]).flatMap fields) =
      (fields target).getD index 0 := by
  let guardedRow := SupportedLastRepresentativeEqualityRows.row
    (base.map some) (values candidates) target
  have rowLength : guardedRow.length = (values candidates ++ [none]).length := by
    simp [guardedRow, SupportedLastRepresentativeEqualityRows.row,
      LastRepresentativeEqualityRows.equalityRow]
  have aligned := blocksAligned width fields fieldLength guardedRow
    (values candidates ++ [none]) rowLength
  have expanded :=
    DelimitedBinaryWordFixedFieldRowExpansion.lookup_row_flatten
      width index guardedRow
      ((values candidates ++ [none]).map fields) indexLt aligned
  change lookup
      (DelimitedBinaryWordFixedFieldRowExpansion.row width index guardedRow)
      (((values candidates ++ [none]).map fields).flatten) = _
  rw [expanded]
  let datum : Option Value → Nat := fun value => (fields value).getD index 0
  rw [List.map_map]
  change lookup guardedRow
      ((values candidates ++ [none]).map datum) = datum target
  rw [List.map_append]
  simp only [List.map_cons, List.map_nil]
  unfold guardedRow SupportedLastRepresentativeEqualityRows.row
  have selected := lookup_equalityRow_map datum
    (values candidates) target targetMem
  unfold lookup at selected ⊢
  simp only [supported, not_true_eq_false, decide_false]
  rw [lookupAux_append_false_append_value_of_length_eq]
  · simpa [LastRepresentativeEqualityRows.equalityRow,
      StableOccurrenceRanks.equalityRow] using selected
  · simp [LastRepresentativeEqualityRows.equalityRow]

/-- Expanding every self-supported representative row into fixed field rows
and looking up candidate-major blocks returns every selected value's complete
field block in stable deduplication order. -/
theorem lookups_fixedFieldRows_selfSupported
    (candidates : List (Candidate Value))
    (supportEq : ∀ candidate ∈ candidates,
      candidate.supported = candidate.value.isSome)
    (fields : Option Value → List Nat) (width : Nat)
    (fieldLength : ∀ value, (fields value).length = width) :
    lookups
        (DelimitedBinaryWordFixedFieldRowExpansion.rows width
          (selectedRows candidates)).words
        ((values candidates ++ [none]).flatMap fields) =
      (candidates.filterMap Candidate.value).dedup.flatMap
        (fun value => fields (some value)) := by
  let active := candidates.filterMap Candidate.value
  have correct : CorrectSupport active candidates :=
    correctSupport_filterMap_of_supported_eq_isSome candidates supportEq
  rw [selectedRows_eq active candidates correct]
  have valuesFilterMap : (values candidates).filterMap id = active := by
    unfold active values
    rw [List.filterMap_map]
    rfl
  have retainAll :
      active.dedup.filter (fun value => decide (value ∈ active)) =
        active.dedup := by
    apply List.filter_eq_self.mpr
    intro value valueMember
    simp only [decide_eq_true_eq]
    exact List.mem_dedup.mp valueMember
  have retainedEq :
      (values candidates).dedup.filter
          (fun value => decide (value ∈ active.map some)) =
        active.dedup.map some := by
    rw [List.dedup_filter_mem_map_some_eq, valuesFilterMap, retainAll]
  rw [retainedEq]
  unfold DelimitedBinaryWordFixedFieldRowExpansion.rows lookups
  simp only [List.map_flatMap, List.flatMap_map, List.map_map,
    Function.comp_apply]
  change
    active.dedup.flatMap (fun selected =>
      (List.range width).map fun index =>
        lookup
          (DelimitedBinaryWordFixedFieldRowExpansion.row width index
            (SupportedLastRepresentativeEqualityRows.row
              (active.map some) (values candidates) (some selected)))
          ((values candidates ++ [none]).flatMap fields)) =
      active.dedup.flatMap (fun value => fields (some value))
  apply List.flatMap_congr
  intro selected selectedMember
  have activeMember : selected ∈ active := List.mem_dedup.mp selectedMember
  have targetMem : some selected ∈ values candidates := by
    have compactMember :
        selected ∈ (values candidates).filterMap id := by
      rw [valuesFilterMap]
      exact activeMember
    rcases List.mem_filterMap.mp compactMember with
      ⟨value, valueMember, valueEq⟩
    simpa using valueEq ▸ valueMember
  have supported : some selected ∈ active.map some := by
    simpa using activeMember
  calc
    (List.range width).map (fun index =>
        lookup
          (DelimitedBinaryWordFixedFieldRowExpansion.row width index
            (SupportedLastRepresentativeEqualityRows.row
              (active.map some) (values candidates) (some selected)))
          ((values candidates ++ [none]).flatMap fields)) =
      (List.range width).map (fun index =>
        (fields (some selected)).getD index 0) := by
          apply List.map_congr_left
          intro index indexMember
          exact lookup_expanded_supportedRow active candidates fields
            width index fieldLength (List.mem_range.mp indexMember)
            (some selected) targetMem supported
    _ = fields (some selected) := by
      simpa [fieldLength (some selected)] using
        List.map_range_getD (fields (some selected)) 0

end PaddedSupportedLastRepresentativeEqualityRows
end LeanTrominoes
