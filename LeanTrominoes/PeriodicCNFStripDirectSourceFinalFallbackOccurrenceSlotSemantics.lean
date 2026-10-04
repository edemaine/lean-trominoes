/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFProgramSource
import LeanTrominoes.AlignedRetainedTerminalSlotFilterBlockSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalFallbackOccurrenceMaskFamilySemantics

/-! # Exact semantic carrier and bend occurrence-slot streams -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


local instance directFinalFallbackSlotSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The compiled carrier control mask selects exactly the flattened stable
terminal slots of the final retained-carrier family. -/
theorem directSourceFinalCarrierOccurrenceSlots_eq_stableRankSlots
    (symbols : List encoding.Γ) :
    directSourceFinalCarrierOccurrenceSlots decider symbols =
      directSourceFinalCarrierStableRankSlots decider symbols := by
  unfold directSourceFinalCarrierOccurrenceSlots
    directSourceFinalCarrierOccurrenceMask
  rw [directSourceFinalFallbackOccurrenceMask_eq_slotReplicates,
    directSourceFinalGlobalTerminalSlots_eq_fourFamilies]
  exact
    AlignedRetainedTerminalSlotFilter.selected_four_blocks_carrier
      (directSourceFinalCrossoverStableRankSlots decider symbols)
      (directSourceFinalCarrierStableRankSlots decider symbols)
      (directSourceFinalBendStableRankSlots decider symbols)
      (directSourceFinalRoutedStableRankSlots decider symbols)

/-- The compiled bend control mask selects exactly the flattened stable
terminal slots of the canonical final base-bend family. -/
theorem directSourceFinalBendOccurrenceSlots_eq_stableRankSlots
    (symbols : List encoding.Γ) :
    directSourceFinalBendOccurrenceSlots decider symbols =
      directSourceFinalBendStableRankSlots decider symbols := by
  unfold directSourceFinalBendOccurrenceSlots
    directSourceFinalBendOccurrenceMask
  rw [directSourceFinalFallbackOccurrenceMask_eq_slotReplicates,
    directSourceFinalGlobalTerminalSlots_eq_fourFamilies]
  exact
    AlignedRetainedTerminalSlotFilter.selected_four_blocks_bend
      (directSourceFinalCrossoverStableRankSlots decider symbols)
      (directSourceFinalCarrierStableRankSlots decider symbols)
      (directSourceFinalBendStableRankSlots decider symbols)
      (directSourceFinalRoutedStableRankSlots decider symbols)

end LeanTrominoes.PeriodicCNFStripReduction

end
