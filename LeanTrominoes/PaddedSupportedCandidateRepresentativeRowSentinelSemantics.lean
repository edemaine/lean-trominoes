/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateRepresentativeRowData
import LeanTrominoes.PaddedSupportedCandidateWordSentinelDedupSemantics
import LeanTrominoes.PaddedSupportedLastRepresentativeSelectionSemantics
import LeanTrominoes.PaddedSupportedValueEqualityRowSemantics

/-! # The one final sentinel representative row -/

namespace LeanTrominoes.PaddedSupportedCandidateWords

open PaddedSupportedLastRepresentativeEqualityRows

variable {Value : Type*} [DecidableEq Value]

/-- The raw guarded-word selector returns exactly the established supported
candidate representatives followed by the sentinel's own equality row. -/
theorem representativeRowsWithSentinel_eq_selectedRows_append
    (encodeValue : Value → List Bool)
    (encodeInjective : Function.Injective encodeValue)
    (base : List Value) (candidates : List (Candidate Value))
    (correct : CorrectSupport base candidates) :
    representativeRowsWithSentinel encodeValue candidates =
      ⟨(selectedRows candidates).words ++
        [LastRepresentativeEqualityRows.equalityRow
          (wordsWithSentinel encodeValue candidates).words
          sentinelWord]⟩ := by
  unfold representativeRowsWithSentinel equalityRowsWithSentinel
  rw [LastRepresentativeEqualityRows.rows_equalityRows]
  congr 1
  rw [dedup_wordsWithSentinel
      encodeValue encodeInjective base candidates correct,
    List.map_append, List.map_singleton, List.map_map,
    selectedRows_eq base candidates correct]
  apply congrArg₂ (fun first last => first ++ [last])
  · apply List.map_congr_left
    intro value valueMember
    have filtered := List.mem_filter.mp valueMember
    have candidateMember : value ∈ values candidates :=
      List.mem_dedup.mp filtered.1
    have supportedMember : value ∈ base.map some := by
      simpa using filtered.2
    exact equalityRow_valueWord_eq_supportedRow
      encodeValue encodeInjective base candidates correct value
      candidateMember supportedMember
  · rfl

end LeanTrominoes.PaddedSupportedCandidateWords
