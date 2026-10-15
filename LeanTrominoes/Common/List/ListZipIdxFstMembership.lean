/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.List.Basic

/-! # First-component membership in indexed lists -/

namespace LeanTrominoes

/-- Every list member occurs as the first component of a pair in `zipIdx`,
at any starting index. -/
theorem exists_mem_zipIdx_fst
    {Value : Type*} (values : List Value) (start : Nat)
    {value : Value} (valueMember : value ∈ values) :
    ∃ index, (value, index) ∈ values.zipIdx start := by
  induction values generalizing start with
  | nil => simp at valueMember
  | cons head tail induction =>
      simp only [List.mem_cons] at valueMember
      rcases valueMember with rfl | valueMember
      · exact ⟨start, by simp⟩
      · rcases induction (start + 1) valueMember with ⟨index, member⟩
        exact ⟨index, by simp [member]⟩

end LeanTrominoes
