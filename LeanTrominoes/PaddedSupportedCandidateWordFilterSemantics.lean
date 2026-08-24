/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateWordSupportSemantics
import LeanTrominoes.PaddedSupportedValueWordSemantics

/-! # Filter semantics of guarded padded-candidate words -/

namespace LeanTrominoes.PaddedSupportedCandidateWords

open PaddedSupportedLastRepresentativeEqualityRows

variable {Value : Type*} [DecidableEq Value]

/-- Removing sentinel words after encoding is exactly filtering candidate
slots by their support bits before encoding. -/
theorem filter_guardedWords_ne_sentinelWord
    (encodeValue : Value → List Bool)
    (base : List Value) (candidates : List (Candidate Value))
    (correct : CorrectSupport base candidates) :
    (candidates.map (guardedWord encodeValue)).filter
        (fun word => decide (word ≠ sentinelWord)) =
      (candidates.filter Candidate.supported).map
        (guardedWord encodeValue) := by
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro candidate member
  have sentinelIff := guardedWord_eq_sentinelWord_iff
    encodeValue base candidates correct candidate member
  cases supported : candidate.supported with
  | false =>
      have wordEq : guardedWord encodeValue candidate = sentinelWord :=
        sentinelIff.mpr supported
      simp [wordEq]
  | true =>
      have wordNe : guardedWord encodeValue candidate ≠ sentinelWord := by
        intro wordEq
        have supportFalse := sentinelIff.mp wordEq
        simp [supported] at supportFalse
      simp [wordNe]

/-- Filtering candidates by their support bits and then projecting values is
the same ordered list as projecting first and testing base membership. -/
theorem map_value_filter_supported
    (base : List Value) (candidates : List (Candidate Value))
    (correct : CorrectSupport base candidates) :
    (candidates.filter Candidate.supported).map Candidate.value =
      (values candidates).filter
        (fun value => decide (value ∈ base.map some)) := by
  unfold values
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro candidate member
  exact correct candidate member

end LeanTrominoes.PaddedSupportedCandidateWords
