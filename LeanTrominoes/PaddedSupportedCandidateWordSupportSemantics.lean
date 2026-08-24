/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateWordData

/-! # Support semantics of guarded padded-candidate words -/

namespace LeanTrominoes.PaddedSupportedCandidateWords

open PaddedSupportedLastRepresentativeEqualityRows

variable {Value : Type*} [DecidableEq Value]

/-- Under the support invariant, a slot is tagged supported exactly when its
optional value belongs to the lifted base family. -/
theorem supported_eq_true_iff_mem
    (base : List Value) (candidates : List (Candidate Value))
    (correct : CorrectSupport base candidates)
    (candidate : Candidate Value) (member : candidate ∈ candidates) :
    candidate.supported = true ↔
      candidate.value ∈ base.map some := by
  rw [correct candidate member]
  simp

/-- A correctly tagged candidate uses the common sentinel word exactly when
it is unsupported. -/
theorem guardedWord_eq_sentinelWord_iff
    (encodeValue : Value → List Bool)
    (base : List Value) (candidates : List (Candidate Value))
    (correct : CorrectSupport base candidates)
    (candidate : Candidate Value) (member : candidate ∈ candidates) :
    guardedWord encodeValue candidate = sentinelWord ↔
      candidate.supported = false := by
  rcases candidate with ⟨value, supported⟩
  cases supported with
  | false => simp [guardedWord, sentinelWord]
  | true =>
      have valueMember : value ∈ base.map some :=
        (supported_eq_true_iff_mem base candidates correct
          ⟨value, true⟩ member).mp rfl
      rcases List.mem_map.mp valueMember with
        ⟨value, _valueMember, valueEq⟩
      subst valueEq
      simp [guardedWord, sentinelWord]

/-- Consequently, comparison with the appended sentinel is exactly the
negated support bit used as the final rejection column. -/
theorem decide_guardedWord_eq_sentinelWord
    (encodeValue : Value → List Bool)
    (base : List Value) (candidates : List (Candidate Value))
    (correct : CorrectSupport base candidates)
    (candidate : Candidate Value) (member : candidate ∈ candidates) :
    decide (guardedWord encodeValue candidate = sentinelWord) =
      !candidate.supported := by
  cases supportedEq : candidate.supported <;>
    simp [guardedWord_eq_sentinelWord_iff encodeValue base candidates
      correct candidate member, supportedEq]

end LeanTrominoes.PaddedSupportedCandidateWords
