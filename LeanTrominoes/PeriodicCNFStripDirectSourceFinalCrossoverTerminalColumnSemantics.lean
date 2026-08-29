/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalCrossoverTerminalChoices
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalDirectTerminalColumnData
import LeanTrominoes.RetainedAngularFanFinalDirectClauseTerminalColumnRouteChoiceSemantics

/-! # Actual terminal-column semantics of direct-source crossovers -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplit.TerminalCoordinateComponents

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalCrossoverTerminalSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalCrossoverTerminalSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The compiled crossover terminal coordinates are exactly the actual
unscaled coordinates of the crossover clause prefix. -/
theorem directSourceFinalCrossoverTerminalCoordinates_eq_actual
    (symbols : List encoding.Γ) :
    retainedFinalDirectTerminalCoordinates
        (directRetainedFinalCrossoverClauseQueries decider symbols) =
      retainedFinalTerminalCoordinatesFrom
        (PeriodicOrthocrossing.finalCoordinatedSourceRoutes
          (directSourceFormula decider symbols)) 0
        (directSourceFinalCrossoverClauses decider symbols) := by
  rw [directRetainedFinalCrossoverClauseQueries_eq_indexed]
  exact retainedFinalDirectTerminalCoordinates_indexedFrom_eq_actual_of_routeChoices
    (directSourceFormula decider symbols) 0
    (directSourceFinalCrossoverClauses decider symbols)
    (directSourceFinalCrossoverClauses_widthAtMostThree decider symbols)
    (directSourceFinalCrossoverRouteChoices decider symbols)

/-- The compiled crossover direction ranks are the direction projection of
that actual coordinate prefix. -/
theorem directSourceFinalCrossoverTerminalDirectionRanks_eq_actual
    (symbols : List encoding.Γ) :
    directSourceFinalCrossoverTerminalDirectionRanks decider symbols =
      directionRanks
        (retainedFinalTerminalCoordinatesFrom
          (PeriodicOrthocrossing.finalCoordinatedSourceRoutes
            (directSourceFormula decider symbols)) 0
          (directSourceFinalCrossoverClauses decider symbols)) := by
  unfold directSourceFinalCrossoverTerminalDirectionRanks
    retainedFinalDirectTerminalDirectionRanks directionRanks
  rw [directSourceFinalCrossoverTerminalCoordinates_eq_actual]

/-- The compiled crossover radial lengths are the radial projection of the
same actual coordinate prefix. -/
theorem directSourceFinalCrossoverTerminalRadialLengths_eq_actual
    (symbols : List encoding.Γ) :
    directSourceFinalCrossoverTerminalRadialLengths decider symbols =
      radialLengths
        (retainedFinalTerminalCoordinatesFrom
          (PeriodicOrthocrossing.finalCoordinatedSourceRoutes
            (directSourceFormula decider symbols)) 0
          (directSourceFinalCrossoverClauses decider symbols)) := by
  unfold directSourceFinalCrossoverTerminalRadialLengths
    retainedFinalDirectTerminalRadialLengths radialLengths
  rw [directSourceFinalCrossoverTerminalCoordinates_eq_actual]

end LeanTrominoes.PeriodicCNFStripReduction

end
