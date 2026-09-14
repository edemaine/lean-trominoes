/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.CompletionMinorBoundaryRelations
import LeanTrominoes.CompletionLBricks

noncomputable section
namespace LeanTrominoes.CompletionPattern.LBricks

set_option maxHeartbeats 0
set_option maxRecDepth 16384

def minorBoundary : Finset Cell := {(2,0),(8,0),(2,6),(8,6)}

def minorOutside (top bottom : Bool) : Finset Cell :=
  {(if top then 8 else 2,0),(if bottom then 2 else 8,6)}

theorem minor_boundary_exhaustive : ∀ outside ∈ minorBoundary.powerset,
    ∃ i : Fin 16, outside = LEqBoundary.outside i := by decide +kernel

theorem minor_boundary_data (i : Fin 16) :
    LEqBoundary.outside i = LNegBoundary.outside i ∧
    LEqBoundary.outside i = LPlugTopBoundary.outside i ∧
    LEqBoundary.outside i = LPlugBotBoundary.outside i := by
  revert i
  decide +kernel

/-- Unlike an equal subbrick, a not subbrick forces both connectors to be Boolean. -/
theorem neg_states (outside : Finset Cell) (subset : outside ⊆ minorBoundary) :
    LNegBoundary.pattern.Completable outside ↔
      ∃ top : Bool, outside = minorOutside top (!top) := by
  obtain ⟨i,rfl⟩ := minor_boundary_exhaustive outside (Finset.mem_powerset.mpr subset)
  rw [(minor_boundary_data i).1,l_neg_boundary]
  revert i
  decide +kernel

theorem plug_top_states (outside : Finset Cell) (subset : outside ⊆ minorBoundary) :
    LPlugTopBoundary.pattern.Completable outside ↔
      ∃ bottom : Bool, outside = minorOutside false bottom := by
  obtain ⟨i,rfl⟩ := minor_boundary_exhaustive outside (Finset.mem_powerset.mpr subset)
  rw [(minor_boundary_data i).2.1,l_plugtop_boundary]
  revert i
  decide +kernel

theorem plug_bottom_states (outside : Finset Cell) (subset : outside ⊆ minorBoundary) :
    LPlugBotBoundary.pattern.Completable outside ↔
      ∃ top : Bool, outside = minorOutside top false := by
  obtain ⟨i,rfl⟩ := minor_boundary_exhaustive outside (Finset.mem_powerset.mpr subset)
  rw [(minor_boundary_data i).2.2,l_plugbot_boundary]
  revert i
  decide +kernel

/-- A Boolean connector at one end of an equal subbrick forces an equal
Boolean connector at its other end. -/
theorem equal_states (outside : Finset Cell) (subset : outside ⊆ minorBoundary)
    (proper : ((2,0) ∈ outside ↔ (8,0) ∉ outside) ∨
      ((2,6) ∈ outside ↔ (8,6) ∉ outside)) :
    LEqBoundary.pattern.Completable outside ↔
      ∃ value : Bool, outside = minorOutside value value := by
  obtain ⟨i,rfl⟩ := minor_boundary_exhaustive outside (Finset.mem_powerset.mpr subset)
  rw [l_eq_boundary]
  have checked : ∀ j : Fin 16,
      (((2,0) ∈ LEqBoundary.outside j ↔ (8,0) ∉ LEqBoundary.outside j) ∨
       ((2,6) ∈ LEqBoundary.outside j ↔ (8,6) ∉ LEqBoundary.outside j)) →
      ((j = 3 ∨ j = 6 ∨ j = 9 ∨ j = 12) ↔
       ∃ value : Bool, LEqBoundary.outside j = minorOutside value value) := by decide +kernel
  exact checked i proper

end LeanTrominoes.CompletionPattern.LBricks
