/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.List.Defs

/-! # Flat maps with one potentially nonempty entry -/

namespace List

/-- A flat map with one potentially nonempty value reduces to that uniquely
indexed value. -/
theorem flatMap_eq_selected_of_unique
    {Index Output : Type*}
    (indices : List Index) (function : Index → List Output)
    (selected : Index)
    (nodup : indices.Nodup)
    (selectedMember : selected ∈ indices)
    (othersEmpty :
      ∀ index ∈ indices, index ≠ selected → function index = []) :
    indices.flatMap function = function selected := by
  induction indices with
  | nil => simp at selectedMember
  | cons index indices induction =>
      rw [List.nodup_cons] at nodup
      rcases List.mem_cons.mp selectedMember with selectedHead | selectedTail
      · subst index
        rw [List.flatMap_cons]
        have tailEmpty : indices.flatMap function = [] := by
          apply List.flatMap_eq_nil_iff.mpr
          intro other otherMember
          exact othersEmpty other (by simp [otherMember]) fun otherEq =>
            nodup.1 (otherEq ▸ otherMember)
        rw [tailEmpty, List.append_nil]
      · have headNe : index ≠ selected := by
          intro headEq
          exact nodup.1 (headEq ▸ selectedTail)
        rw [List.flatMap_cons,
          othersEmpty index (by simp) headNe,
          List.nil_append]
        exact induction nodup.2 selectedTail fun other otherMember otherNe =>
          othersEmpty other (by simp [otherMember]) otherNe

end List
