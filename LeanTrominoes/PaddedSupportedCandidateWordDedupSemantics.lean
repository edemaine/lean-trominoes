/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListDedupFilter
import LeanTrominoes.PaddedSupportedCandidateWordFilterSemantics

/-! # Stable deduplication of guarded padded-candidate words -/

namespace LeanTrominoes.PaddedSupportedCandidateWords

open PaddedSupportedLastRepresentativeEqualityRows

variable {Value : Type*} [DecidableEq Value]

/-- After restricting to supported candidates, guarded candidate words are
exactly the tagged words of the corresponding supported optional values. -/
theorem map_guardedWord_filter_supported
    (encodeValue : Value → List Bool)
    (base : List Value) (candidates : List (Candidate Value))
    (correct : CorrectSupport base candidates) :
    (candidates.filter Candidate.supported).map
        (guardedWord encodeValue) =
      ((values candidates).filter
        (fun value => decide (value ∈ base.map some))).map
          (valueWord encodeValue) := by
  rw [← map_value_filter_supported base candidates correct,
    List.map_map]
  apply List.map_congr_left
  intro candidate member
  have supported : candidate.supported = true :=
    List.mem_filter.mp member |>.2
  exact guardedWord_eq_valueWord_of_supported
    encodeValue candidate supported

/-- Deduplicating non-sentinel guarded words is therefore exactly stable
deduplication and support filtering of optional candidate values, transported
through the injective tagged encoding. -/
theorem dedup_filter_guardedWords_ne_sentinelWord
    (encodeValue : Value → List Bool)
    (encodeInjective : Function.Injective encodeValue)
    (base : List Value) (candidates : List (Candidate Value))
    (correct : CorrectSupport base candidates) :
    ((candidates.map (guardedWord encodeValue)).filter
        (fun word => decide (word ≠ sentinelWord))).dedup =
      ((values candidates).dedup.filter
        (fun value => decide (value ∈ base.map some))).map
          (valueWord encodeValue) := by
  rw [filter_guardedWords_ne_sentinelWord
      encodeValue base candidates correct,
    map_guardedWord_filter_supported
      encodeValue base candidates correct,
    List.dedup_map_of_injective
      (valueWord_injective encodeValue encodeInjective),
    List.dedup_filter]

end LeanTrominoes.PaddedSupportedCandidateWords
