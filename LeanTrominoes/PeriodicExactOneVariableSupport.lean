/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicOneInThreeNoUnitsOccurrences

/-! # Original support survives the two exact-one replacements -/
namespace LeanTrominoes

theorem PeriodicOneInThree.original_mem {V : Type*} [DecidableEq V]
    (source : PeriodicCNF V) (width : source.WidthAtMost 3)
    {atom : V} (member : atom ∈ source.variableOccurrences) :
    Sum.inl atom ∈ (formula source).variableOccurrences := by
  apply List.count_pos_iff.mp
  rw [formula_variableOccurrences_count_original source width atom]
  exact List.count_pos_iff.mpr member

theorem PeriodicOneInThreeNoUnits.original_mem {V : Type*} [DecidableEq V]
    (source : PeriodicCNF V) {atom : V} (member : atom ∈ source.variableOccurrences) :
    Sum.inl atom ∈ (formula source).variableOccurrences := by
  apply List.count_pos_iff.mp
  rw [formula_variableOccurrences_count_original source atom]
  exact List.count_pos_iff.mpr member

theorem PeriodicOneInThreeNoUnits.composed_variableCount_le {V : Type*} [DecidableEq V]
    (source : PeriodicCNF V) (width : source.WidthAtMost 3) :
    source.variableOccurrences.dedup.length ≤
      (formula (PeriodicOneInThree.formula source)).variableOccurrences.length := by
  let embedding : V → OneInThreeNoUnitVariable (OneInThreeVariable V) := fun a => .inl (.inl a)
  have injective : Function.Injective embedding := by intro a b h; cases h; rfl
  have nodup := (List.nodup_dedup source.variableOccurrences).map injective
  have subset : source.variableOccurrences.dedup.map embedding ⊆
      (formula (PeriodicOneInThree.formula source)).variableOccurrences := by
    intro a ha
    obtain ⟨original,originalMember,rfl⟩ := List.mem_map.mp ha
    exact original_mem _ (PeriodicOneInThree.original_mem source width (List.mem_dedup.mp originalMember))
  simpa only [List.length_map] using (nodup.subperm subset).length_le

end LeanTrominoes
