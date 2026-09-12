/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryFieldBooleanFilterNativeListCompiler

/-! # Select one value from each nonempty constant block -/

namespace LeanTrominoes.UnaryFieldBooleanFilter

/-- Keep the first field of a block and reject all its later fields. -/
def firstBlockControls (count : Nat) : List Bool :=
  (List.range count).map fun index => decide (index = 0)

private theorem selected_false_replicate (count value : Nat) :
    DelimitedBinaryWordBooleanFilter.selected (List.replicate count false) (List.replicate count value) = [] := by
  induction count with
  | zero => rfl
  | succ count ih => simpa [List.replicate_succ, DelimitedBinaryWordBooleanFilter.selected] using ih

theorem firstBlockControls_succ (count : Nat) :
    firstBlockControls (count + 1) = true :: List.replicate count false := by
  simp [firstBlockControls, List.range_succ_eq_map, List.map_map, Function.comp_def]

/-- A repeated coordinate contributes exactly one selected field. -/
theorem selectedValues_firstBlock (count value : Nat) (positive : 0 < count) :
    selectedValues (firstBlockControls count) (List.replicate count value) = [value] := by
  cases count with
  | zero => omega
  | succ count =>
      rw [firstBlockControls_succ, selectedValues_eq]
      simp [List.replicate_succ, DelimitedBinaryWordBooleanFilter.selected, selected_false_replicate]

/-- A clause-major stream of repeated coordinates collapses to one field
per clause while preserving clause order. -/
theorem selectedValues_firstBlocks {Block : Type} (blocks : List Block)
    (count : Block → Nat) (value : Block → Nat)
    (positive : ∀ block ∈ blocks, 0 < count block) :
    selectedValues (blocks.flatMap fun block => firstBlockControls (count block))
      (blocks.flatMap fun block => List.replicate (count block) (value block)) = blocks.map value := by
  rw [selectedValues_flatMap blocks (fun block => firstBlockControls (count block))
    (fun block => List.replicate (count block) (value block))
    (fun block _ => by simp [firstBlockControls])]
  apply (List.flatMap_congr ?_).trans (List.map_eq_flatMap.symm)
  intro block member
  exact selectedValues_firstBlock _ _ (positive block member)

end LeanTrominoes.UnaryFieldBooleanFilter
