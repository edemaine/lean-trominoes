/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCrossoverTerminalColumnSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierTerminalColumnSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalBendTerminalColumnSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalRoutedTerminalColumnSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalTerminalColumnData
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalTerminalCoordinateFamilySemantics

/-! # Actual semantics of the complete final direction column -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplit.TerminalCoordinateComponents

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalDirectionColumnStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalDirectionColumnVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The complete compiled five-family direction column is exactly the
direction projection of every actual final terminal coordinate. -/
theorem directSourceFinalTerminalDirectionRanks_eq_actual
    (symbols : List encoding.Γ) :
    directSourceFinalTerminalDirectionRanks decider symbols =
      directionRanks
        (retainedFinalTerminalCoordinatesFrom
          (PeriodicOrthocrossing.finalCoordinatedSourceRoutes
            (directSourceFormula decider symbols)) 0
          (deduplicatedClauses
            (directSourceFormula decider symbols))) := by
  rw [directSourceFinalTerminalCoordinates_eq_families]
  unfold directSourceFinalTerminalDirectionRanks
    directSourceFinalCarrierTerminalDirectionRankSuffix
    directSourceFinalBendRoutedTerminalDirectionRanks
    directionRanks
  simp only [List.map_append]
  rw [directSourceFinalCrossoverTerminalDirectionRanks_eq_actual,
    directSourceFinalCarrierTerminalDirectionRanks_eq_actual,
    directSourceFinalBendTerminalDirectionRanks_eq_actual,
    directSourceFinalRoutedTerminalDirectionRanks_eq_actual]
  rfl

end LeanTrominoes.PeriodicCNFStripReduction

end
