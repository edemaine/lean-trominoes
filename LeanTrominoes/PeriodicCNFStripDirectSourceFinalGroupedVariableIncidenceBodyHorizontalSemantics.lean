/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableIncidenceColumnHorizontalSemantics
import LeanTrominoes.PeriodicCNFStripGroupedVariableIncidenceTypedShapeHorizontalSemantics

/-! # Complete variable-incidence bodies agree with canonical horizontal routes -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open Gadget PeriodicThreeDM PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  sourceVariableDecidableEq
  horizontalRibbonInnerVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- Every compiled variable-incidence body is the actual horizontal route
word, in canonical variable-triple and red/green/blue order. -/
theorem directSourceFinalGroupedVariableIncidenceBodies_eq_horizontal
    (symbols : List encoding.Γ) :
    directSourceFinalGroupedVariableIncidenceBodies decider symbols =
      (variableTriples (horizontalSemanticNormalizedRibbonSource
        (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols)).erase).flatMap
        fun triple => incidenceColors.map fun color => unitSubdivisionDirections
          (horizontalTypedIncidenceRouteComputed
            ((PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols, triple), color)) := by
  rw [directSourceFinalGroupedVariableIncidenceBodies_eq_horizontalTypedShape,
    variableTriples_eq_occurrenceEntries_flatMap, List.flatMap_assoc]
  apply List.flatMap_congr
  intro entry member
  exact groupedVariableIncidenceTypedShapeBodies_eq_horizontalRoutes
    (PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider symbols) entry member

end LeanTrominoes.PeriodicCNFStripReduction

end
