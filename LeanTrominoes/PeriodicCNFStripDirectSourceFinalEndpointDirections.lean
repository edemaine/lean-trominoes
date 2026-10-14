/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFProgramSource
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalPresentedDirectionWords
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalVariableOccurrenceData
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRouteHeaderClauseDirectionSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedOccurrenceRoutePairSemantics

/-! # Direct fan endpoint columns use the actual horizontal route words -/

noncomputable section

set_option maxHeartbeats 800000

namespace LeanTrominoes.PeriodicCNFStripReduction

open Gadget PeriodicOrthocrossing
open PeriodicOneInThreePolarityNormalizationRouteSubdivision

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)


local instance directEndpointVariableDecidableEq : DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- The variable fan input directions are the opposite final directions of
the actual stored horizontal routes, in the same presentation order. -/
theorem directSourceFinalVariableOccurrenceData_directions_eq_horizontal
    (symbols : List encoding.Γ) :
    (directSourceFinalVariableOccurrenceData decider symbols).map
        HorizontalRoutedRouteHeader.OccurrenceData.direction =
      (presentedIncidenceDirectionWords
        (horizontalRoutedFormulaComputed
          (PeriodicCNF.ProgramSource.formulaOfSymbols decider symbols))
        (horizontalRoutedRoutesComputed
          (PeriodicCNF.ProgramSource.formulaOfSymbols decider symbols))).map
          (fun word => (word.getLastD .invalid).opposite) := by
  rw [directSourceFinalVariableOccurrenceData_eq_routePairs,
    ← directFigureNinePolarityRoutePairs_map_directions_eq_horizontal,
    List.map_map, List.map_map]
  rfl

end LeanTrominoes.PeriodicCNFStripReduction

end
