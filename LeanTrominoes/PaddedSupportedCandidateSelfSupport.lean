/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedLastRepresentativeEqualityRows

/-! # Candidate streams supported by their own active values -/

namespace LeanTrominoes.PaddedSupportedLastRepresentativeEqualityRows

variable {Value : Type*} [DecidableEq Value]

/-- If support is exactly option activity, then the candidate stream is
correctly supported by the ordered list of all its active values. -/
theorem correctSupport_filterMap_of_supported_eq_isSome
    (candidates : List (Candidate Value))
    (supportEq : ∀ candidate ∈ candidates,
      candidate.supported = candidate.value.isSome) :
    CorrectSupport (candidates.filterMap Candidate.value) candidates := by
  intro candidate candidateMember
  rw [supportEq candidate candidateMember]
  cases valueEq : candidate.value with
  | none => simp
  | some value =>
      simp
      exact ⟨candidate, candidateMember, valueEq⟩

end LeanTrominoes.PaddedSupportedLastRepresentativeEqualityRows
