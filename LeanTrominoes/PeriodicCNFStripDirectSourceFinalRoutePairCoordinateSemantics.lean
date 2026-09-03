/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineRoutePrefixCoordinateSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalColoredRoutedRequestBlockSemantics

/-! # Template coordinates of direct final Figure 9 route pairs -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalRoutePairCoordinateStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalRoutePairCoordinateVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Direct header/tail pairs retain the exact finite-template coordinate
schedule of the retained source descriptors; dynamic tails do not affect it. -/
theorem directFigureNinePolarityRoutePairs_map_headerTemplateCoordinate
    (symbols : List encoding.Γ) :
    (directFigureNinePolarityRoutePairs decider symbols).map (fun pair =>
        FormulaShapeFigureNineRoutePrefix.headerTemplateCoordinate pair.1) =
      (FormulaShapeRetainedFigureNineDirection.descriptors
        (directSourceFormula decider symbols)).flatMap
          FormulaShapeFigureNineRoutePrefix.expectedHeaderTemplateCoordinateBlock := by
  unfold directFigureNinePolarityRoutePairs
  exact
    FormulaShapeFigureNineRoutePrefix.sourcePairs_map_headerTemplateCoordinate
      _ _

end LeanTrominoes.PeriodicCNFStripReduction

end
