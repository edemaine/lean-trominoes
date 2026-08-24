/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListDedupAppendSingleton
import LeanTrominoes.PaddedSupportedCandidateWordDedupSemantics

/-! # Stable deduplication after appending the rejection sentinel -/

namespace LeanTrominoes.PaddedSupportedCandidateWords

open PaddedSupportedLastRepresentativeEqualityRows

variable {Value : Type*} [DecidableEq Value]

/-- The last-occurrence representatives of all guarded words consist of the
supported optional-value representatives in exact order, followed by the one
explicit rejection sentinel. -/
theorem dedup_wordsWithSentinel
    (encodeValue : Value → List Bool)
    (encodeInjective : Function.Injective encodeValue)
    (base : List Value) (candidates : List (Candidate Value))
    (correct : CorrectSupport base candidates) :
    (wordsWithSentinel encodeValue candidates).words.dedup =
      ((values candidates).dedup.filter
        (fun value => decide (value ∈ base.map some))).map
          (valueWord encodeValue) ++ [sentinelWord] := by
  unfold wordsWithSentinel
  rw [List.dedup_append_singleton_eq_filter,
    dedup_filter_guardedWords_ne_sentinelWord
      encodeValue encodeInjective base candidates correct]

end LeanTrominoes.PaddedSupportedCandidateWords
