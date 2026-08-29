/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCrossoverTerminalColumnSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCarrierTerminalRadialSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalBendTerminalRadialSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalRoutedTerminalColumnSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalTerminalColumnData
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalTerminalCoordinateFamilySemantics

/-! # Actual semantics of the complete final radial column -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplit.TerminalCoordinateComponents

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalRadialColumnStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalRadialColumnVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The complete compiled five-family radial column is exactly the radial
projection of every actual final terminal coordinate. -/
theorem directSourceFinalTerminalRadialLengths_eq_actual
    (symbols : List encoding.Γ) :
    directSourceFinalTerminalRadialLengths decider symbols =
      radialLengths
        (retainedFinalTerminalCoordinatesFrom
          (PeriodicOrthocrossing.finalCoordinatedSourceRoutes
            (directSourceFormula decider symbols)) 0
          (deduplicatedClauses
            (directSourceFormula decider symbols))) := by
  rw [directSourceFinalTerminalCoordinates_eq_families]
  unfold directSourceFinalTerminalRadialLengths
    directSourceFinalCarrierTerminalRadialSuffix
    directSourceFinalBendRoutedTerminalRadialLengths
    radialLengths
  simp only [List.map_append]
  rw [directSourceFinalCrossoverTerminalRadialLengths_eq_actual,
    directSourceFinalCarrierTerminalRadialLengths_eq_actual,
    directSourceFinalBendTerminalRadialLengths_eq_actual,
    directSourceFinalRoutedTerminalRadialLengths_eq_actual]
  rfl

end LeanTrominoes.PeriodicCNFStripReduction

end
