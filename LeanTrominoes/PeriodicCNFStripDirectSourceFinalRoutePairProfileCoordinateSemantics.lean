/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineRoutePrefixProfileCoordinateSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalColoredRoutedRequestBlockSemantics

/-! # Profile-qualified coordinates of direct final Figure 9 route pairs -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalRoutePairProfileCoordinateStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalRoutePairProfileCoordinateVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

/-- Direct header/tail pairs retain the parent clause profile together with
their exact finite-template coordinate schedule. -/
theorem directFigureNinePolarityRoutePairs_map_headerTemplateProfileCoordinate
    (symbols : List encoding.Γ) :
    (directFigureNinePolarityRoutePairs decider symbols).map (fun pair =>
        FormulaShapeFigureNineRoutePrefix.headerTemplateProfileCoordinate
          pair.1) =
      (FormulaShapeRetainedFigureNineDirection.descriptors
        (directSourceFormula decider symbols)).flatMap
          FormulaShapeFigureNineRoutePrefix.expectedHeaderTemplateProfileCoordinateBlock := by
  unfold directFigureNinePolarityRoutePairs
  exact
    FormulaShapeFigureNineRoutePrefix.sourcePairs_map_headerTemplateProfileCoordinate
      _ _

end LeanTrominoes.PeriodicCNFStripReduction

end
