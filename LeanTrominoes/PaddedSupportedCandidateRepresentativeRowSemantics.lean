/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateRepresentativeRowSentinelSemantics

/-! # Semantics of guarded padded-candidate representative rows -/

namespace LeanTrominoes.PaddedSupportedCandidateWords

open PaddedSupportedLastRepresentativeEqualityRows

variable {Value : Type*} [DecidableEq Value]

/-- Removing the one final sentinel row makes guarded-word representative
selection exactly the established padded support-aware selection. -/
theorem representativeRows_eq_selectedRows
    (encodeValue : Value → List Bool)
    (encodeInjective : Function.Injective encodeValue)
    (base : List Value) (candidates : List (Candidate Value))
    (correct : CorrectSupport base candidates) :
    representativeRows encodeValue candidates = selectedRows candidates := by
  unfold representativeRows
  rw [representativeRowsWithSentinel_eq_selectedRows_append
    encodeValue encodeInjective base candidates correct]
  simp

end LeanTrominoes.PaddedSupportedCandidateWords
