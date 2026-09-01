/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectRetainedFiniteDirectionDescriptorData
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalClauseFrameCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalColoredRoutedRequestBlockSemantics

/-! # Alignment of direct Figure 9 route pairs and occurrence headers -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicCNF

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

noncomputable local instance directFinalRoutePairHeaderSemanticsStackFintype
    (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

local instance directFinalRoutePairHeaderSemanticsVariableDecidableEq :
    DecidableEq Variable :=
  directSourceVariableDecidableEq

private theorem variableMarkers_cycleClauseDescriptors
    {Value : Type} (values : List Value) :
    (List.replicate values.length
        FormulaShapeDirectionOrdering.Token.variable).flatMap
        directSourceFinalCycleClauseDescriptorBlock =
      values.flatMap fun _ =>
        FormulaShapeFixedEightDirection.cycleClauseDescriptors := by
  induction values with
  | nil => rfl
  | cons value values induction =>
      simp only [List.length_cons]
      rw [List.replicate_succ, List.flatMap_cons, List.flatMap_cons]
      change
        FormulaShapeFixedEightDirection.cycleClauseDescriptors ++
            (List.replicate values.length
              FormulaShapeDirectionOrdering.Token.variable).flatMap
              directSourceFinalCycleClauseDescriptorBlock =
          FormulaShapeFixedEightDirection.cycleClauseDescriptors ++
            values.flatMap fun _ =>
              FormulaShapeFixedEightDirection.cycleClauseDescriptors
      rw [induction]

/-- The compiled copied/cycle descriptor prefix and the retained descriptor
stream expand to the same exact header list.  The latter's final variable
markers deliberately emit no headers. -/
theorem directSourceFinalClauseHeaders_eq_retained
    (symbols : List encoding.Γ) :
    FormulaShapeFigureNinePolarityRouteHeader.sourceHeaders
        (directSourceFinalClauseDescriptors decider symbols) =
      FormulaShapeFigureNinePolarityRouteHeader.sourceHeaders
        (FormulaShapeRetainedFigureNineDirection.descriptors
          (directSourceFormula decider symbols)) := by
  rw [show
    FormulaShapeRetainedFigureNineDirection.descriptors
        (directSourceFormula decider symbols) =
      directRetainedFigureNineFiniteDirectionDescriptors
        decider symbols by
    change directRetainedFigureNineDirectionDescriptors decider symbols = _
    exact directRetainedFigureNineDirectionDescriptors_eq_finite
      decider symbols]
  unfold directSourceFinalClauseDescriptors
    directRetainedFigureNineCopiedClauseDescriptors
    directSourceFinalCycleClauseDescriptors
    directRetainedFigureNineFiniteSourceVariableMarkers
    directRetainedFigureNineFiniteDirectionDescriptors
    FormulaShapeRetainedFigureNineDirection.finiteDescriptors
    FormulaShapeRetainedFigureNineDirection.finiteCycleClauseDescriptors
  rw [variableMarkers_cycleClauseDescriptors]
  simp [FormulaShapeFigureNinePolarityRouteHeader.sourceHeaders,
    FormulaShapeFigureNinePolarityRouteHeader.tokenBlock]

/-- The clause-frame compiler and the explicit route-pair source carry the
same retained header at every occurrence position. -/
theorem directSourceFinalClauseFrames_map_header_eq_routePairs
    (symbols : List encoding.Γ) :
    (directSourceFinalClauseFrames decider symbols).map
        HorizontalRoutedRouteHeaderClauseFrame.Data.header =
      (directFigureNinePolarityRoutePairs decider symbols).map Prod.fst := by
  unfold directSourceFinalClauseFrames
  rw [HorizontalRoutedRouteHeaderClauseFrame.output_map_header]
  unfold directFigureNinePolarityRoutePairs
  rw [PeriodicCNF.FormulaShapeFigureNinePolarityRouteTail.sourcePairs_map_fst]
  exact directSourceFinalClauseHeaders_eq_retained decider symbols

end LeanTrominoes.PeriodicCNFStripReduction

end
