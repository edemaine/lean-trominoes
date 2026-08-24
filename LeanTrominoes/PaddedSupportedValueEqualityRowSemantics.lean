/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateEqualityRowSemantics
import LeanTrominoes.PaddedSupportedValueWordSemantics

/-! # Equality rows of retained optional-value words -/

namespace LeanTrominoes.PaddedSupportedCandidateWords

open PaddedSupportedLastRepresentativeEqualityRows

variable {Value : Type*} [DecidableEq Value]

/-- Every supported optional value presented by the candidates has exactly
the established support-guarded equality row when represented by its tagged
word in the sentinel-extended matrix. -/
theorem equalityRow_valueWord_eq_supportedRow
    (encodeValue : Value → List Bool)
    (encodeInjective : Function.Injective encodeValue)
    (base : List Value) (candidates : List (Candidate Value))
    (correct : CorrectSupport base candidates)
    (value : Option Value)
    (valueCandidate : value ∈ values candidates)
    (valueSupported : value ∈ base.map some) :
    LastRepresentativeEqualityRows.equalityRow
        (wordsWithSentinel encodeValue candidates).words
        (valueWord encodeValue value) =
      SupportedLastRepresentativeEqualityRows.row
        (base.map some) (values candidates) value := by
  unfold values at valueCandidate
  rcases List.mem_map.mp valueCandidate with
    ⟨candidate, candidateMember, candidateValue⟩
  subst value
  have candidateSupported : candidate.supported = true := by
    rw [correct candidate candidateMember]
    simp [valueSupported]
  rw [← guardedWord_eq_valueWord_of_supported
    encodeValue candidate candidateSupported]
  change equalityRowWithSentinel encodeValue candidates candidate = _
  rw [equalityRowWithSentinel_eq_row_of_supported
    encodeValue encodeInjective base candidates correct
    candidate candidateMember candidateSupported]
  unfold PaddedSupportedLastRepresentativeEqualityRows.row
    SupportedLastRepresentativeEqualityRows.row
  simp [candidateSupported, valueSupported]

end LeanTrominoes.PaddedSupportedCandidateWords
