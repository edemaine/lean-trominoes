/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionIGuardedRelations
import LeanTrominoes.CompletionIBricks

noncomputable section
namespace LeanTrominoes.CompletionPattern.IBricks

set_option maxHeartbeats 0
set_option maxRecDepth 16384

def minorBoundary : Finset Cell := {(5,0),(14,0),(5,27),(14,27)}

def minorOutside (top bottom : Bool) : Finset Cell :=
  {(if top then 14 else 5,0),(if bottom then 5 else 14,27)}

theorem minor_boundary_exhaustive : ∀ outside ∈ minorBoundary.powerset,
    ∃ i : Fin 16, outside = IGuardedEqBoundary.outside i := by decide +kernel

theorem minor_boundary_data (i : Fin 16) :
    IGuardedEqBoundary.outside i = IGuardedNegBoundary.outside i ∧
    IGuardedEqBoundary.outside i = IGuardedPlugTopBoundary.outside i ∧
    IGuardedEqBoundary.outside i = IGuardedPlugBotBoundary.outside i := by
  revert i
  decide +kernel

/-- Unlike an equal subbrick, a not subbrick forces both connectors to be Boolean. -/
theorem neg_states (outside : Finset Cell) (subset : outside ⊆ minorBoundary) :
    IGuardedNegBoundary.pattern.Completable outside ↔
      ∃ top : Bool, outside = minorOutside top (!top) := by
  obtain ⟨i,rfl⟩ := minor_boundary_exhaustive outside (Finset.mem_powerset.mpr subset)
  rw [(minor_boundary_data i).1,i_guarded_neg_boundary]
  revert i
  decide +kernel

theorem plug_top_states (outside : Finset Cell) (subset : outside ⊆ minorBoundary) :
    IGuardedPlugTopBoundary.pattern.Completable outside ↔
      ∃ bottom : Bool, outside = minorOutside false bottom := by
  obtain ⟨i,rfl⟩ := minor_boundary_exhaustive outside (Finset.mem_powerset.mpr subset)
  rw [(minor_boundary_data i).2.1,i_guarded_plugtop_boundary]
  revert i
  decide +kernel

theorem plug_bottom_states (outside : Finset Cell) (subset : outside ⊆ minorBoundary) :
    IGuardedPlugBotBoundary.pattern.Completable outside ↔
      ∃ top : Bool, outside = minorOutside top false := by
  obtain ⟨i,rfl⟩ := minor_boundary_exhaustive outside (Finset.mem_powerset.mpr subset)
  rw [(minor_boundary_data i).2.2,i_guarded_plugbot_boundary]
  revert i
  decide +kernel

/-- A Boolean connector at one end of an equal subbrick forces an equal
Boolean connector at its other end. -/
theorem equal_states (outside : Finset Cell) (subset : outside ⊆ minorBoundary)
    (proper : ((5,0) ∈ outside ↔ (14,0) ∉ outside) ∨
      ((5,27) ∈ outside ↔ (14,27) ∉ outside)) :
    IGuardedEqBoundary.pattern.Completable outside ↔
      ∃ value : Bool, outside = minorOutside value value := by
  obtain ⟨i,rfl⟩ := minor_boundary_exhaustive outside (Finset.mem_powerset.mpr subset)
  rw [i_guarded_eq_boundary]
  have checked : ∀ j : Fin 16,
      (((5,0) ∈ IGuardedEqBoundary.outside j ↔ (14,0) ∉ IGuardedEqBoundary.outside j) ∨
       ((5,27) ∈ IGuardedEqBoundary.outside j ↔ (14,27) ∉ IGuardedEqBoundary.outside j)) →
      ((j = 3 ∨ j = 6 ∨ j = 9 ∨ j = 12) ↔
       ∃ value : Bool, IGuardedEqBoundary.outside j = minorOutside value value) := by decide +kernel
  exact checked i proper

end LeanTrominoes.CompletionPattern.IBricks
