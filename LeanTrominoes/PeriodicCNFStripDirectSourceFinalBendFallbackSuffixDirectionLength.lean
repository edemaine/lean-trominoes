/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalBendTerminalColumnSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalFallbackSuffixQueryData
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalStableRankSlotCoordinateLength

/-! # Bend fallback direction-count alignment -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalBendFallbackDirectionLengthStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalBendFallbackDirectionLengthVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

theorem directSourceFinalBendDirectionRanks_length_eq_coordinates
    (symbols : List encoding.Γ) :
    (directSourceBaseBendTerminalDirectionRanks decider symbols).length =
      (directSourceFinalBendFallbackTerminalCoordinates
        decider symbols).length := by
  rw [directSourceFinalBendTerminalDirectionRanks_eq_actual]
  unfold directSourceFinalBendFallbackTerminalCoordinates
    TerminalCoordinateComponents.directionRanks
  simp only [List.length_map]
  exact
    retainedFinalTerminalCoordinatesFrom_finalRoutes_length_irrel
      (directSourceFormula decider symbols)
      (directSourceFinalBendStart decider symbols)
      (directSourceFinalBendClauses decider symbols) _ _

end LeanTrominoes.PeriodicCNFStripReduction

end
