/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateWordSupportSemantics

/-! # Equality semantics of guarded padded-candidate words -/

namespace LeanTrominoes.PaddedSupportedCandidateWords

open PaddedSupportedLastRepresentativeEqualityRows

variable {Value : Type*} [DecidableEq Value]

/-- From a supported source slot, equality of guarded injective encodings is
exactly equality of the option-valued candidate payloads.  Unsupported target
slots cannot carry the same value by correctness of their support tags. -/
theorem guardedWord_eq_iff_value_eq_of_supported
    (encodeValue : Value → List Bool)
    (encodeInjective : Function.Injective encodeValue)
    (base : List Value) (candidates : List (Candidate Value))
    (correct : CorrectSupport base candidates)
    (first second : Candidate Value)
    (firstMember : first ∈ candidates)
    (secondMember : second ∈ candidates)
    (firstSupported : first.supported = true) :
    guardedWord encodeValue first = guardedWord encodeValue second ↔
      first.value = second.value := by
  rcases first with ⟨firstValue, firstSupport⟩
  cases firstSupport with
  | false => simp at firstSupported
  | true =>
      have firstValueMember : firstValue ∈ base.map some :=
        (supported_eq_true_iff_mem base candidates correct
          ⟨firstValue, true⟩ firstMember).mp rfl
      rcases List.mem_map.mp firstValueMember with
        ⟨firstValue, firstValueBaseMember, firstValueEq⟩
      subst firstValueEq
      rcases second with ⟨secondValue, secondSupport⟩
      cases secondSupport with
      | false =>
          have secondValueNotMember :
              secondValue ∉ base.map some := by
            intro secondValueMember
            have correctSecond := correct
              ⟨secondValue, false⟩ secondMember
            simp [secondValueMember] at correctSecond
          have firstOptionMember :
              some firstValue ∈ base.map some :=
            List.mem_map.mpr
              ⟨firstValue, firstValueBaseMember, rfl⟩
          have valuesNe : some firstValue ≠ secondValue := by
            intro valuesEq
            exact secondValueNotMember (valuesEq ▸ firstOptionMember)
          simp [guardedWord, valuesNe]
      | true =>
          have secondValueMember : secondValue ∈ base.map some :=
            (supported_eq_true_iff_mem base candidates correct
              ⟨secondValue, true⟩ secondMember).mp rfl
          rcases List.mem_map.mp secondValueMember with
            ⟨secondValue, _secondValueBaseMember, secondValueEq⟩
          subst secondValueEq
          constructor
          · intro wordsEq
            have encodedEq :
                encodeValue firstValue = encodeValue secondValue :=
              List.cons.inj wordsEq |>.2
            exact congrArg some (encodeInjective encodedEq)
          · intro valuesEq
            injection valuesEq with valueEq
            simp [guardedWord, valueEq]

end LeanTrominoes.PaddedSupportedCandidateWords
