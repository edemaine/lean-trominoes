/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFProgramSource
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierTerminalColumnSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalFallbackSuffixQueryData
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalStableRankSlotCoordinateLength

/-! # Carrier fallback direction-count alignment -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


local instance directFinalCarrierFallbackDirectionLengthVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

theorem directSourceFinalCarrierDirectionRanks_length_eq_coordinates
    (symbols : List encoding.Γ) :
    (directSourceCarrierTerminalDirectionRanks decider symbols).length =
      (directSourceFinalCarrierFallbackTerminalCoordinates
        decider symbols).length := by
  rw [directSourceFinalCarrierTerminalDirectionRanks_eq_actual]
  unfold directSourceFinalCarrierFallbackTerminalCoordinates
    TerminalCoordinateComponents.directionRanks
  simp only [List.length_map]
  exact
    retainedFinalTerminalCoordinatesFrom_finalRoutes_length_irrel
      (directSourceFormula decider symbols)
      (directSourceFinalCarrierStart decider symbols)
      (directSourceFinalCarrierClauses decider symbols) _ _

end LeanTrominoes.PeriodicCNFStripReduction

end
