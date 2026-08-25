/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateSelfSupport
import LeanTrominoes.PaddedSupportedLastRepresentativeSelectionSemantics
import LeanTrominoes.LastTrueUnaryValueLookupAlignedTrailingFalseSemantics
import LeanTrominoes.LastTrueUnaryValueLookupSemantics
import LeanTrominoes.ListOptionSupportedDedup

/-! # Unary lookups from aligned active candidate values -/

namespace LeanTrominoes
namespace LastTrueUnaryValueLookupMachine

variable {Value : Type*} [DecidableEq Value]

/-- An equality row may look through arbitrary inactive data, provided every
column equal to the selected target carries the requested datum. -/
theorem lookup_equalityRow_of_forall₂
    (values : List Value) (data : List Nat) (target : Value)
    (targetDatum : Nat) (targetMem : target ∈ values)
    (aligned : List.Forall₂
      (fun value datum => value = target → datum = targetDatum)
      values data) :
    lookup (StableOccurrenceRanks.equalityRow values target) data =
      targetDatum := by
  unfold lookup
  induction aligned with
  | nil => simp at targetMem
  | @cons value datum values data headAligned aligned induction =>
      by_cases same : target = value
      · subst value
        have datumEq : datum = targetDatum := headAligned rfl
        subst datum
        by_cases later : target ∈ values
        · have irrelevant :=
            lookupAux_equalityRow_candidate_irrelevant
              targetDatum 0 target values data later
          simpa [StableOccurrenceRanks.equalityRow, lookupAux] using
            (irrelevant.trans (induction later))
        · have unchanged :=
            lookupAux_equalityRow_of_not_mem
              targetDatum target values data later
          simpa [StableOccurrenceRanks.equalityRow, lookupAux] using unchanged
      · have later : target ∈ values := by
          simpa [same] using targetMem
        simpa [StableOccurrenceRanks.equalityRow, lookupAux, same] using
          induction later

end LastTrueUnaryValueLookupMachine

namespace PaddedSupportedLastRepresentativeEqualityRows

variable {Value : Type*}

/-- Candidate/data alignment descends to the candidates' optional values. -/
theorem forall₂_values_of_active_alignment
    (candidates : List (Candidate Value)) (data : List Nat)
    (datum : Value → Nat)
    (aligned : List.Forall₂
      (fun candidate value => ∀ active,
        candidate.value = some active → value = datum active)
      candidates data)
    (selected : Value) :
    List.Forall₂
      (fun value field => value = some selected → field = datum selected)
      (values candidates) data := by
  unfold values
  induction aligned with
  | nil => exact List.Forall₂.nil
  | @cons candidate field candidates data headAligned aligned induction =>
      exact List.Forall₂.cons
        (fun equal => headAligned selected equal) induction

variable [DecidableEq Value]

/-- Representative rows ignore arbitrary data in inactive candidate slots.
Only active columns need agree with the datum attached to their value. -/
theorem lookups_selectedRows_selfSupported_aligned_append_value
    (candidates : List (Candidate Value)) (data : List Nat)
    (supportEq : ∀ candidate ∈ candidates,
      candidate.supported = candidate.value.isSome)
    (datum : Value → Nat)
    (aligned : List.Forall₂
      (fun candidate value => ∀ active,
        candidate.value = some active → value = datum active)
      candidates data)
    (sentinel : Nat) :
    LastTrueUnaryValueLookupMachine.lookups
        (selectedRows candidates).words (data ++ [sentinel]) =
      (candidates.filterMap Candidate.value).dedup.map datum := by
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
  unfold LastTrueUnaryValueLookupMachine.lookups
  rw [retainedEq, List.map_map]
  change _ = active.dedup.map datum
  rw [List.map_map]
  apply List.map_congr_left
  intro selected selectedMember
  have activeMember : selected ∈ active :=
    List.mem_dedup.mp selectedMember
  have candidateMember : some selected ∈ values candidates := by
    have compactMember :
        selected ∈ (values candidates).filterMap id := by
      rw [valuesFilterMap]
      exact activeMember
    rcases List.mem_filterMap.mp compactMember with
      ⟨value, valueMember, valueEq⟩
    simpa using valueEq ▸ valueMember
  simp only [Function.comp_apply]
  unfold SupportedLastRepresentativeEqualityRows.row
  have valuesAligned := forall₂_values_of_active_alignment
    candidates data datum aligned selected
  have selectedLookup :=
    LastTrueUnaryValueLookupMachine.lookup_equalityRow_of_forall₂
      (values candidates) data (some selected) (datum selected)
      candidateMember valuesAligned
  unfold LastTrueUnaryValueLookupMachine.lookup at selectedLookup ⊢
  simp only [List.mem_map, Option.some.injEq, exists_eq_right,
    activeMember, not_true_eq_false, decide_false]
  rw [LastTrueUnaryValueLookupMachine.lookupAux_append_false_append_value_of_length_eq]
  · simpa [LastRepresentativeEqualityRows.equalityRow,
      StableOccurrenceRanks.equalityRow] using selectedLookup
  · simpa [LastRepresentativeEqualityRows.equalityRow,
      StableOccurrenceRanks.equalityRow, values] using aligned.length_eq

end PaddedSupportedLastRepresentativeEqualityRows
end LeanTrominoes
