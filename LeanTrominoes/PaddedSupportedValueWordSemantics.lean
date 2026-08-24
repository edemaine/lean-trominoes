/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedValueWordData

/-! # Semantics of tagged optional-value words -/

namespace LeanTrominoes.PaddedSupportedCandidateWords

open PaddedSupportedLastRepresentativeEqualityRows

variable {Value : Type*}

/-- Injectivity of the underlying value encoding extends to the tagged
optional-value encoding. -/
theorem valueWord_injective
    (encodeValue : Value → List Bool)
    (encodeInjective : Function.Injective encodeValue) :
    Function.Injective (valueWord encodeValue) := by
  intro first second wordsEq
  cases first with
  | none =>
      cases second with
      | none => rfl
      | some second => simp [valueWord, sentinelWord] at wordsEq
  | some first =>
      cases second with
      | none => simp [valueWord, sentinelWord] at wordsEq
      | some second =>
          have encodedEq : encodeValue first = encodeValue second :=
            List.cons.inj wordsEq |>.2
          exact congrArg some (encodeInjective encodedEq)

/-- On a supported candidate, the guarded candidate word is simply the
injective word of its optional value. -/
theorem guardedWord_eq_valueWord_of_supported
    (encodeValue : Value → List Bool)
    (candidate : Candidate Value)
    (supported : candidate.supported = true) :
    guardedWord encodeValue candidate =
      valueWord encodeValue candidate.value := by
  rcases candidate with ⟨value, support⟩
  cases support with
  | false => simp at supported
  | true => cases value <;> rfl

end LeanTrominoes.PaddedSupportedCandidateWords
