/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PositionedPeriodicCNFAnchorNormalization

/-! # Clause-anchor changes preserve locality -/
namespace LeanTrominoes

theorem PeriodicClause.offsetDistance_anchorNormalize {V : Type*}
    (first second : PeriodicLiteral V) (anchor : Cell) :
    offsetDistance (first.anchorNormalize anchor) (second.anchorNormalize anchor) = offsetDistance first second := by
  simp [offsetDistance, PeriodicLiteral.anchorNormalize, Cell.sub, sub_sub_sub_cancel_right]

theorem PeriodicClause.isLocal_anchorNormalize {V : Type*} {source : PeriodicClause V}
    (locality : source.IsLocal) : source.anchorNormalize.IsLocal := by
  intro first hf second hs
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hf
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hs
  rw [offsetDistance_anchorNormalize]
  exact locality a ha b hb

theorem PeriodicCNF.anchorNormalize_local {V : Type*} {source : PeriodicCNF V}
    (locality : source.IsLocal) : source.anchorNormalize.IsLocal := by
  intro clause member
  obtain ⟨original, ho, rfl⟩ := List.mem_map.mp member
  exact PeriodicClause.isLocal_anchorNormalize (locality original ho)

end LeanTrominoes
