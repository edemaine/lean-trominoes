/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateEqualityRowData
import LeanTrominoes.PaddedSupportedCandidateWordEqualitySemantics

/-! # Semantics of supported guarded-candidate equality rows -/

namespace LeanTrominoes.PaddedSupportedCandidateWords

open PaddedSupportedLastRepresentativeEqualityRows

variable {Value : Type*} [DecidableEq Value]

/-- A supported candidate's guarded-word equality row is exactly its padded
support-aware option-equality row.  The appended sentinel comparison supplies
the final false rejection bit. -/
theorem equalityRowWithSentinel_eq_row_of_supported
    (encodeValue : Value → List Bool)
    (encodeInjective : Function.Injective encodeValue)
    (base : List Value) (candidates : List (Candidate Value))
    (correct : CorrectSupport base candidates)
    (candidate : Candidate Value) (member : candidate ∈ candidates)
    (supported : candidate.supported = true) :
    equalityRowWithSentinel encodeValue candidates candidate =
      row candidates candidate := by
  unfold equalityRowWithSentinel wordsWithSentinel row values
    LastRepresentativeEqualityRows.equalityRow
  simp only [List.map_append, List.map_singleton, List.map_map]
  apply congrArg₂ (fun first last => first ++ [last])
  · apply List.map_congr_left
    intro other otherMember
    exact Bool.decide_congr
      (guardedWord_eq_iff_value_eq_of_supported
        encodeValue encodeInjective base candidates correct
        candidate other member otherMember supported)
  · exact decide_guardedWord_eq_sentinelWord
      encodeValue base candidates correct candidate member

end LeanTrominoes.PaddedSupportedCandidateWords
