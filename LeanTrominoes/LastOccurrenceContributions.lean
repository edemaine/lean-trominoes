/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.StableOccurrenceRanksBounds

/-! # Group-size contributions at last occurrences -/

namespace LeanTrominoes
namespace LastOccurrenceContributions

variable {Value : Type*} [DecidableEq Value]

/-- Retain the full multiplicity of a value only at its final presentation. -/
def contributionsAux (all : List Value) : List Value → List Nat
  | [] => []
  | value :: remaining =>
      (if value ∈ remaining then 0 else all.count value) ::
        contributionsAux all remaining

def contributions (values : List Value) : List Nat :=
  contributionsAux values values

@[simp] theorem contributionsAux_length (all remaining : List Value) :
    (contributionsAux all remaining).length = remaining.length := by
  induction remaining with
  | nil => rfl
  | cons value remaining induction =>
      simp [contributionsAux, induction]

@[simp] theorem contributions_length (values : List Value) :
    (contributions values).length = values.length := by
  simp [contributions]

theorem selectedValue_count_append (seen : List Value) (value : Value)
    (remaining : List Value) :
    UnarySuccessorEqualityFilterMachine.selectedValue
        (seen.count value) ((seen ++ value :: remaining).count value) =
      if value ∈ remaining then 0
      else (seen ++ value :: remaining).count value := by
  by_cases member : value ∈ remaining
  · have positive : 0 < remaining.count value :=
      List.count_pos_iff.mpr member
    simp [UnarySuccessorEqualityFilterMachine.selectedValue,
      List.count_append, member]
    omega
  · have zero : remaining.count value = 0 :=
      List.count_eq_zero.mpr member
    simp [UnarySuccessorEqualityFilterMachine.selectedValue,
      List.count_append, member, zero]

def selectedValues_eq_contributionsAux (seen remaining : List Value) :
    UnarySuccessorEqualityFilterMachine.selectedValues
        (StableOccurrenceRanks.ranksAux
          (seen ++ remaining) seen.length remaining)
        (remaining.map fun value => (seen ++ remaining).count value) =
      contributionsAux (seen ++ remaining) remaining := by
  induction remaining generalizing seen with
  | nil => rfl
  | cons value remaining induction =>
      simp only [StableOccurrenceRanks.ranksAux, List.map_cons,
        UnarySuccessorEqualityFilterMachine.selectedValues,
        contributionsAux]
      rw [show (seen ++ value :: remaining).take seen.length = seen by simp]
      rw [selectedValue_count_append]
      congr 1
      simpa [List.append_assoc] using induction (seen ++ [value])

/-- The verified successor predicate selects exactly the last occurrence of
each equality class. -/
theorem selectedValues_stableRanks (values : List Value) :
    UnarySuccessorEqualityFilterMachine.selectedValues
        (StableOccurrenceRanks.ranks values)
        (values.map fun value => values.count value) =
      contributions values := by
  simpa [StableOccurrenceRanks.ranks, contributions] using
    selectedValues_eq_contributionsAux ([] : List Value) values

end LastOccurrenceContributions
end LeanTrominoes
