/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalRoutedClauseTerminalColumnSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalRoutedVariableTerminalColumnSemantics
import LeanTrominoes.RetainedAngularFanFinalTerminalCoordinateFamilyPresentation

/-! # Actual terminal-column semantics of the direct routed suffix -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplit.TerminalCoordinateComponents

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalRoutedTerminalSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalRoutedTerminalSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The compiler's combined routed query suffix is exactly the actual
routed-clause/routed-variable terminal-coordinate suffix. -/
theorem directSourceFinalRoutedTerminalCoordinates_eq_actual
    (symbols : List encoding.Γ) :
    retainedFinalDirectTerminalCoordinates
        (directRetainedFinalRoutedClauseQuerySuffix decider symbols) =
      retainedFinalTerminalCoordinatesFrom
        (PeriodicOrthocrossing.finalCoordinatedSourceRoutes
          (directSourceFormula decider symbols))
        (directSourceFinalRoutedClauseStart decider symbols)
        (directSourceFinalRoutedClauseClauses decider symbols ++
          directSourceFinalRoutedVariableClauses decider symbols) := by
  unfold directRetainedFinalRoutedClauseQuerySuffix
    retainedFinalDirectTerminalCoordinates
  rw [List.flatMap_append]
  change retainedFinalDirectTerminalCoordinates
      (directRetainedFinalRoutedClauseQueries decider symbols) ++
    retainedFinalDirectTerminalCoordinates
      (directRetainedFinalRoutedVariableClauseQueries decider symbols) = _
  rw [directSourceFinalRoutedClauseTerminalCoordinates_eq_actual,
    directSourceFinalRoutedVariableTerminalCoordinates_eq_actual,
    retainedFinalTerminalCoordinatesFrom_append]
  rfl

/-- The existing compiled routed direction suffix is the direction
projection of that actual coordinate suffix. -/
theorem directSourceFinalRoutedTerminalDirectionRanks_eq_actual
    (symbols : List encoding.Γ) :
    directSourceFinalRoutedTerminalDirectionRanks decider symbols =
      directionRanks
        (retainedFinalTerminalCoordinatesFrom
          (PeriodicOrthocrossing.finalCoordinatedSourceRoutes
            (directSourceFormula decider symbols))
          (directSourceFinalRoutedClauseStart decider symbols)
          (directSourceFinalRoutedClauseClauses decider symbols ++
            directSourceFinalRoutedVariableClauses decider symbols)) := by
  unfold directSourceFinalRoutedTerminalDirectionRanks
    retainedFinalDirectTerminalDirectionRanks directionRanks
  rw [directSourceFinalRoutedTerminalCoordinates_eq_actual]

/-- The existing compiled routed radial suffix is the radial projection of
the same actual coordinate suffix. -/
theorem directSourceFinalRoutedTerminalRadialLengths_eq_actual
    (symbols : List encoding.Γ) :
    directSourceFinalRoutedTerminalRadialLengths decider symbols =
      radialLengths
        (retainedFinalTerminalCoordinatesFrom
          (PeriodicOrthocrossing.finalCoordinatedSourceRoutes
            (directSourceFormula decider symbols))
          (directSourceFinalRoutedClauseStart decider symbols)
          (directSourceFinalRoutedClauseClauses decider symbols ++
            directSourceFinalRoutedVariableClauses decider symbols)) := by
  unfold directSourceFinalRoutedTerminalRadialLengths
    retainedFinalDirectTerminalRadialLengths radialLengths
  rw [directSourceFinalRoutedTerminalCoordinates_eq_actual]

end LeanTrominoes.PeriodicCNFStripReduction

end
