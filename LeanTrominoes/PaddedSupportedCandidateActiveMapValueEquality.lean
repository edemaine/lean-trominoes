/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateActiveMap

/-! # Equality preservation under activity-supported candidate maps -/

namespace LeanTrominoes.PaddedSupportedLastRepresentativeEqualityRows

universe u v w

variable {Source : Type u} {First : Type v} {Second : Type w}

/-- Two projections induce the same equality relation on optional values
drawn from a fixed padded candidate stream. -/
theorem option_map_eq_iff_of_eq_iff_on_filterMap
    (firstProject : Source → First) (secondProject : Source → Second)
    (candidates : List (Candidate Source))
    (sameEquality :
      ∀ first ∈ candidates.filterMap Candidate.value,
        ∀ second ∈ candidates.filterMap Candidate.value,
          firstProject first = firstProject second ↔
            secondProject first = secondProject second)
    (firstCandidate secondCandidate : Candidate Source)
    (firstCandidateMember : firstCandidate ∈ candidates)
    (secondCandidateMember : secondCandidate ∈ candidates) :
    firstCandidate.value.map firstProject =
        secondCandidate.value.map firstProject ↔
      firstCandidate.value.map secondProject =
        secondCandidate.value.map secondProject := by
  cases firstValue : firstCandidate.value with
  | none =>
      cases secondCandidate.value <;> simp
  | some first =>
      cases secondValue : secondCandidate.value with
      | none => simp
      | some second =>
          have firstValueMember :
              first ∈ candidates.filterMap Candidate.value :=
            List.mem_filterMap.mpr
              ⟨firstCandidate, firstCandidateMember, firstValue⟩
          have secondValueMember :
              second ∈ candidates.filterMap Candidate.value :=
            List.mem_filterMap.mpr
              ⟨secondCandidate, secondCandidateMember, secondValue⟩
          simpa using
            sameEquality first firstValueMember second secondValueMember

end LeanTrominoes.PaddedSupportedLastRepresentativeEqualityRows
