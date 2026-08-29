/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalFallbackOccurrenceSlotSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalFallbackSuffixQueryData
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalStableRankSlotCoordinateLength

/-! # Carrier fallback slot-count alignment -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCarrierFallbackOccurrenceLengthStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalCarrierFallbackOccurrenceLengthVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

theorem directSourceFinalCarrierOccurrenceSlots_length_eq_coordinates
    (symbols : List encoding.Γ) :
    (directSourceFinalCarrierOccurrenceSlots decider symbols).length =
      (directSourceFinalCarrierFallbackTerminalCoordinates
        decider symbols).length := by
  rw [directSourceFinalCarrierOccurrenceSlots_eq_stableRankSlots]
  unfold directSourceFinalCarrierStableRankSlots
    directSourceFinalCarrierStableRankSlotBlocks
    directSourceFinalCarrierFallbackTerminalCoordinates
  exact
    directSourceFinalStableRankSlotBlocksFrom_flatten_length_eq_coordinates
      decider symbols _ _ _

end LeanTrominoes.PeriodicCNFStripReduction

end
