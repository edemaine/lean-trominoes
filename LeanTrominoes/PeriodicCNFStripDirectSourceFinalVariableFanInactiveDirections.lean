/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableFanStableSemantics

/-! # Canonical directions of inactive direct variable-fan slots -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM PlanarThreeDM

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- Every unused slot in the clause-major fan stream has the horizontal
semantic north fallback. -/
theorem directSourceFinalVariableFanData_direction_of_inactive
    (symbols : List encoding.Γ) (fan : VariableRibbonFanData)
    (member : fan ∈ directSourceFinalVariableFanData decider symbols)
    (slot : VariableSiteSlot) (inactive : ¬ fan.SlotActive slot) :
    fan.direction slot = .north := by
  rw [directSourceFinalVariableFanData_eq_map_stableFan] at member
  obtain ⟨value, _, rfl⟩ := List.mem_map.mp member
  exact FinalFanDataTripleAssembler.stableFan_direction_of_inactive _ _ _ _ slot inactive

/-- Regrouping by variable preserves the same canonical inactive directions. -/
theorem directSourceFinalGroupedVariableFanData_direction_of_inactive
    (symbols : List encoding.Γ) (fan : VariableRibbonFanData)
    (member : fan ∈ directSourceFinalGroupedVariableFanData decider symbols)
    (slot : VariableSiteSlot) (inactive : ¬ fan.SlotActive slot) :
    fan.direction slot = .north := by
  rw [directSourceFinalGroupedVariableFanData_eq_map_stableFan] at member
  obtain ⟨key, _, rfl⟩ := List.mem_map.mp member
  exact FinalFanDataTripleAssembler.stableFan_direction_of_inactive _ _ _ _ slot inactive

end LeanTrominoes.PeriodicCNFStripReduction

end
