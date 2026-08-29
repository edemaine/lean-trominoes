/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseFamilyStarts
import LeanTrominoes.RetainedAngularFanFinalTerminalCoordinateFamilyPresentation

/-! # Five-family presentation of direct-source terminal coordinates -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection
open PeriodicEightOccurrenceSplit

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCoordinateFamilyStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalCoordinateFamilyVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Actual terminal coordinates of the final duplicate-free clause list split
exactly into crossover, carrier, bend, and combined routed blocks. -/
theorem directSourceFinalTerminalCoordinates_eq_families
    (symbols : List encoding.Γ) :
    retainedFinalTerminalCoordinatesFrom
        (PeriodicOrthocrossing.finalCoordinatedSourceRoutes
          (directSourceFormula decider symbols)) 0
        (deduplicatedClauses
          (directSourceFormula decider symbols)) =
      retainedFinalTerminalCoordinatesFrom
          (PeriodicOrthocrossing.finalCoordinatedSourceRoutes
            (directSourceFormula decider symbols)) 0
          (directSourceFinalCrossoverClauses decider symbols) ++
        (retainedFinalTerminalCoordinatesFrom
            (PeriodicOrthocrossing.finalCoordinatedSourceRoutes
              (directSourceFormula decider symbols))
            (directSourceFinalCarrierStart decider symbols)
            (directSourceFinalCarrierClauses decider symbols) ++
          (retainedFinalTerminalCoordinatesFrom
              (PeriodicOrthocrossing.finalCoordinatedSourceRoutes
                (directSourceFormula decider symbols))
              (directSourceFinalBendStart decider symbols)
              (directSourceFinalBendClauses decider symbols) ++
            retainedFinalTerminalCoordinatesFrom
              (PeriodicOrthocrossing.finalCoordinatedSourceRoutes
                (directSourceFormula decider symbols))
              (directSourceFinalRoutedClauseStart decider symbols)
              (directSourceFinalRoutedClauseClauses decider symbols ++
                directSourceFinalRoutedVariableClauses decider symbols))) := by
  have clausesEq :
      deduplicatedClauses (directSourceFormula decider symbols) =
        directSourceFinalCrossoverClauses decider symbols ++
          (directSourceFinalCarrierClauses decider symbols ++
            (directSourceFinalBendClauses decider symbols ++
              (directSourceFinalRoutedClauseClauses decider symbols ++
                directSourceFinalRoutedVariableClauses decider symbols))) := by
    rw [directSource_deduplicatedClauses_eq_fiveFamilies,
      directSourceFinalFiveFamilyClauses_eq_named]
    simp only [List.append_assoc]
  rw [clausesEq,
    retainedFinalTerminalCoordinatesFrom_append,
    retainedFinalTerminalCoordinatesFrom_append,
    retainedFinalTerminalCoordinatesFrom_append]
  simp only [directSourceFinalCarrierStart, directSourceFinalBendStart,
    directSourceFinalRoutedClauseStart, Nat.zero_add, Nat.add_assoc]

end LeanTrominoes.PeriodicCNFStripReduction

end
