/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.List.Nodup

/-! # Selecting one nonempty block from a finite keyed scan -/

namespace LeanTrominoes

/-- A duplicate-free scan whose nonselected entries emit empty blocks equals
the selected entry's block. -/
theorem flatMap_eq_selected_of_nodup
    {Value Output : Type*}
    (values : List Value) (nodup : values.Nodup)
    (blocks : Value → List Output) (selected : Value)
    (selectedMember : selected ∈ values)
    (otherEmpty : ∀ value ∈ values,
      value ≠ selected → blocks value = []) :
    values.flatMap blocks = blocks selected := by
  induction values with
  | nil => simp at selectedMember
  | cons value values induction =>
      have valueNotValues := (List.nodup_cons.mp nodup).1
      have valuesNodup := (List.nodup_cons.mp nodup).2
      rcases List.mem_cons.mp selectedMember with selectedEq | selectedTail
      · subst value
        rw [List.flatMap_cons]
        have tailEmpty : values.flatMap blocks = [] := by
          rw [List.flatMap_eq_nil_iff]
          intro item itemMember
          exact otherEmpty item (by simp [itemMember]) fun itemEq =>
            valueNotValues (itemEq ▸ itemMember)
        rw [tailEmpty, List.append_nil]
      · have valueNe : value ≠ selected := by
          intro valueEq
          exact valueNotValues (valueEq ▸ selectedTail)
        rw [List.flatMap_cons,
          otherEmpty value (by simp) valueNe]
        simp only [List.nil_append]
        apply induction valuesNodup selectedTail
        intro item itemMember itemNe
        exact otherEmpty item (by simp [itemMember]) itemNe

/-- The same selection law when uniqueness is certified after mapping a key. -/
theorem flatMap_eq_selected_of_key_nodup
    {Value Key Output : Type*}
    (values : List Value) (key : Value → Key)
    (keyNodup : (values.map key).Nodup)
    (blocks : Value → List Output) (selected : Value)
    (selectedMember : selected ∈ values)
    (otherEmpty : ∀ value ∈ values,
      key value ≠ key selected → blocks value = []) :
    values.flatMap blocks = blocks selected := by
  apply flatMap_eq_selected_of_nodup values keyNodup.of_map
    blocks selected selectedMember
  intro value valueMember valueNe
  apply otherEmpty value valueMember
  intro keyEq
  exact valueNe (List.inj_on_of_nodup_map keyNodup
    valueMember selectedMember keyEq)

end LeanTrominoes
