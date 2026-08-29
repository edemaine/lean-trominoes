/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalDirectTerminalColumnData
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalRoutedClauseTerminalChoices
import LeanTrominoes.RetainedAngularFanFinalDirectClauseTerminalColumnRouteChoiceSemantics

/-! # Actual terminal-column semantics of direct-source routed clauses -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplit.TerminalCoordinateComponents

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalRoutedClauseTerminalSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalRoutedClauseTerminalSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Numeric direction column of the routed-clause query family alone. -/
def directSourceFinalRoutedClauseTerminalDirectionRanks
    (symbols : List encoding.Γ) : List Nat :=
  retainedFinalDirectTerminalDirectionRanks
    (directRetainedFinalRoutedClauseQueries decider symbols)

/-- Numeric radial column of the routed-clause query family alone. -/
def directSourceFinalRoutedClauseTerminalRadialLengths
    (symbols : List encoding.Γ) : List Nat :=
  retainedFinalDirectTerminalRadialLengths
    (directRetainedFinalRoutedClauseQueries decider symbols)

/-- The compiled routed-clause terminal coordinates are exactly the actual
unscaled coordinates at their global positions in the final clause list. -/
theorem directSourceFinalRoutedClauseTerminalCoordinates_eq_actual
    (symbols : List encoding.Γ) :
    retainedFinalDirectTerminalCoordinates
        (directRetainedFinalRoutedClauseQueries decider symbols) =
      retainedFinalTerminalCoordinatesFrom
        (PeriodicOrthocrossing.finalCoordinatedSourceRoutes
          (directSourceFormula decider symbols))
        (directSourceFinalRoutedClauseStart decider symbols)
        (directSourceFinalRoutedClauseClauses decider symbols) := by
  rw [directRetainedFinalRoutedClauseQueries_eq_indexed,
    directSourceFinalIndexedRoutedClauseQueries_eq_named,
    directSourceFormula_eq_finalNormalized]
  exact retainedFinalDirectTerminalCoordinates_indexedFrom_eq_actual_of_routeChoices
    (directSourceFinalNormalizedFormula decider symbols)
    (directSourceFinalRoutedClauseStart decider symbols)
    (directSourceFinalRoutedClauseClauses decider symbols)
    (directSourceFinalRoutedClauseClauses_widthAtMostThree decider symbols)
    (directSourceFinalRoutedClauseRouteChoices decider symbols)

/-- The routed-clause direction column is the direction projection of those
actual coordinates. -/
theorem directSourceFinalRoutedClauseTerminalDirectionRanks_eq_actual
    (symbols : List encoding.Γ) :
    directSourceFinalRoutedClauseTerminalDirectionRanks decider symbols =
      directionRanks
        (retainedFinalTerminalCoordinatesFrom
          (PeriodicOrthocrossing.finalCoordinatedSourceRoutes
            (directSourceFormula decider symbols))
          (directSourceFinalRoutedClauseStart decider symbols)
          (directSourceFinalRoutedClauseClauses decider symbols)) := by
  unfold directSourceFinalRoutedClauseTerminalDirectionRanks
    retainedFinalDirectTerminalDirectionRanks directionRanks
  rw [directSourceFinalRoutedClauseTerminalCoordinates_eq_actual]

/-- The routed-clause radial column is the radial projection of the same
actual coordinates. -/
theorem directSourceFinalRoutedClauseTerminalRadialLengths_eq_actual
    (symbols : List encoding.Γ) :
    directSourceFinalRoutedClauseTerminalRadialLengths decider symbols =
      radialLengths
        (retainedFinalTerminalCoordinatesFrom
          (PeriodicOrthocrossing.finalCoordinatedSourceRoutes
            (directSourceFormula decider symbols))
          (directSourceFinalRoutedClauseStart decider symbols)
          (directSourceFinalRoutedClauseClauses decider symbols)) := by
  unfold directSourceFinalRoutedClauseTerminalRadialLengths
    retainedFinalDirectTerminalRadialLengths radialLengths
  rw [directSourceFinalRoutedClauseTerminalCoordinates_eq_actual]

end LeanTrominoes.PeriodicCNFStripReduction

end
