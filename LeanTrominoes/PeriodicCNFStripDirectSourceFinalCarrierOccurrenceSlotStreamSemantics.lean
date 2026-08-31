/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierOccurrenceSlotBlockFamilySemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalFallbackOccurrenceSlotSemantics

/-! # Semantic meaning of the compiled carrier occurrence-slot stream -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCarrierSlotStreamStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalCarrierSlotStreamVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The compiled carrier occurrence-slot stream is the flattened sequence of
semantic occurrence slots in final carrier-clause order. -/
theorem directSourceFinalCarrierOccurrenceSlots_eq_semantic
    (symbols : List encoding.Γ) :
    directSourceFinalCarrierOccurrenceSlots decider symbols =
      (directSourceFinalCarrierSemanticOccurrenceSlotBlocks
        decider symbols).flatten := by
  rw [directSourceFinalCarrierOccurrenceSlots_eq_stableRankSlots]
  unfold directSourceFinalCarrierStableRankSlots
  rw [directSourceFinalCarrierSemanticOccurrenceSlotBlocks_eq]

end LeanTrominoes.PeriodicCNFStripReduction

end
