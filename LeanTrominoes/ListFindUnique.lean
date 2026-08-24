/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListFindBool

/-! # Unique Boolean list lookup -/

namespace LeanTrominoes

/-- If exactly one listed value satisfies a Boolean predicate, first-success
search returns that value. -/
theorem listFind?_eq_some_of_mem_of_unique
    {Value : Type*} (values : List Value)
    (predicate : Value → Bool) (selected : Value)
    (selectedMember : selected ∈ values)
    (selectedTrue : predicate selected = true)
    (unique : ∀ candidate ∈ values,
      predicate candidate = true → candidate = selected) :
    values.find? predicate = some selected := by
  induction values with
  | nil => simp at selectedMember
  | cons head tail induction =>
      by_cases headTrue : predicate head = true
      · have headEq := unique head (by simp) headTrue
        subst head
        simp [selectedTrue]
      · have selectedTail : selected ∈ tail := by
          simp only [List.mem_cons] at selectedMember
          rcases selectedMember with selectedEq | selectedTail
          · subst head
            exact (headTrue selectedTrue).elim
          · exact selectedTail
        have tailUnique : ∀ candidate ∈ tail,
            predicate candidate = true → candidate = selected := by
          intro candidate candidateMember candidateTrue
          exact unique candidate (by simp [candidateMember]) candidateTrue
        simp [headTrue, induction selectedTail tailUnique]

end LeanTrominoes
