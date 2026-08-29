/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalDirectTerminalColumnData
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalRoutedVariableTerminalChoices
import LeanTrominoes.RetainedAngularFanFinalDirectClauseTerminalColumnRouteChoiceSemantics

/-! # Actual terminal-column semantics of direct-source routed variables -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplit.TerminalCoordinateComponents

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalRoutedVariableTerminalSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalRoutedVariableTerminalSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Numeric direction column of the routed-variable query family alone. -/
def directSourceFinalRoutedVariableTerminalDirectionRanks
    (symbols : List encoding.Γ) : List Nat :=
  retainedFinalDirectTerminalDirectionRanks
    (directRetainedFinalRoutedVariableClauseQueries decider symbols)

/-- Numeric radial column of the routed-variable query family alone. -/
def directSourceFinalRoutedVariableTerminalRadialLengths
    (symbols : List encoding.Γ) : List Nat :=
  retainedFinalDirectTerminalRadialLengths
    (directRetainedFinalRoutedVariableClauseQueries decider symbols)

/-- The compiled routed-variable terminal coordinates are exactly the actual
unscaled coordinates at their global positions in the final clause list. -/
theorem directSourceFinalRoutedVariableTerminalCoordinates_eq_actual
    (symbols : List encoding.Γ) :
    retainedFinalDirectTerminalCoordinates
        (directRetainedFinalRoutedVariableClauseQueries decider symbols) =
      retainedFinalTerminalCoordinatesFrom
        (PeriodicOrthocrossing.finalCoordinatedSourceRoutes
          (directSourceFormula decider symbols))
        (directSourceFinalRoutedVariableStart decider symbols)
        (directSourceFinalRoutedVariableClauses decider symbols) := by
  rw [directRetainedFinalRoutedVariableClauseQueries_eq_indexed,
    directSourceFinalIndexedRoutedVariableQueries_eq_named,
    directSourceFormula_eq_finalNormalized]
  exact retainedFinalDirectTerminalCoordinates_indexedFrom_eq_actual_of_routeChoices
    (directSourceFinalNormalizedFormula decider symbols)
    (directSourceFinalRoutedVariableStart decider symbols)
    (directSourceFinalRoutedVariableClauses decider symbols)
    (directSourceFinalRoutedVariableClauses_widthAtMostThree decider symbols)
    (directSourceFinalRoutedVariableRouteChoices decider symbols)

/-- The routed-variable direction column is the direction projection of
those actual coordinates. -/
theorem directSourceFinalRoutedVariableTerminalDirectionRanks_eq_actual
    (symbols : List encoding.Γ) :
    directSourceFinalRoutedVariableTerminalDirectionRanks decider symbols =
      directionRanks
        (retainedFinalTerminalCoordinatesFrom
          (PeriodicOrthocrossing.finalCoordinatedSourceRoutes
            (directSourceFormula decider symbols))
          (directSourceFinalRoutedVariableStart decider symbols)
          (directSourceFinalRoutedVariableClauses decider symbols)) := by
  unfold directSourceFinalRoutedVariableTerminalDirectionRanks
    retainedFinalDirectTerminalDirectionRanks directionRanks
  rw [directSourceFinalRoutedVariableTerminalCoordinates_eq_actual]

/-- The routed-variable radial column is the radial projection of the same
actual coordinates. -/
theorem directSourceFinalRoutedVariableTerminalRadialLengths_eq_actual
    (symbols : List encoding.Γ) :
    directSourceFinalRoutedVariableTerminalRadialLengths decider symbols =
      radialLengths
        (retainedFinalTerminalCoordinatesFrom
          (PeriodicOrthocrossing.finalCoordinatedSourceRoutes
            (directSourceFormula decider symbols))
          (directSourceFinalRoutedVariableStart decider symbols)
          (directSourceFinalRoutedVariableClauses decider symbols)) := by
  unfold directSourceFinalRoutedVariableTerminalRadialLengths
    retainedFinalDirectTerminalRadialLengths radialLengths
  rw [directSourceFinalRoutedVariableTerminalCoordinates_eq_actual]

end LeanTrominoes.PeriodicCNFStripReduction

end
