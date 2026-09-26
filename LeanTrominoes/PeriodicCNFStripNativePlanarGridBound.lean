/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicCNFStripNativePlanarEncoding
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationSize
import LeanTrominoes.PeriodicPlanarExactOneIntrinsicGridSize

/-! # The routed candidate meets the existing exact-one grid-size constant -/
noncomputable section
namespace LeanTrominoes.PeriodicPlanarSAT.ExactOneEndpoint
open PeriodicOrthocrossing
variable {V : Type} [Primcodable V] [DecidableEq V]
local instance strongGridTargetDecidableEq : DecidableEq (Target V) :=
  PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq
set_option maxHeartbeats 800000

omit [Primcodable V] in
theorem source_variables_nine_le_literals (f : PeriodicCNF V) (hl : f.IsLocal) (hw : f.WidthAtMost 3)
    (ho : f.OccurrencesAtMost 3) (hn : ∀ clause ∈ f.clauses, clause ≠ []) :
    9 * f.variableOccurrences.dedup.length ≤ (positioned f).erase.presentationLiteralCount := by
  have sourceBound := ThreeOccurrenceGeometry.source_variables_le_retained f
  have countEq := ThreeOccurrenceGeometry.output_variableCount_eq_retained f
  have exactBound := PeriodicOneInThreeNoUnits.composed_variableCount_le
    (ThreeOccurrenceGeometry.formula f).erase (retainedFigureNineClearancePositionedFormula_widthAtMostThree f hw)
  rw [← retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula_erase,
    ← final_occurrence_length f hl hw ho hn, PeriodicCNF.variableOccurrences_length] at exactBound
  omega

end LeanTrominoes.PeriodicPlanarSAT.ExactOneEndpoint

namespace LeanTrominoes.PeriodicCNFStripReduction
open PeriodicOneInThreePolarityNormalizationRouteSubdivision
attribute [local instance] sourceVariableDecidableEq
  horizontalRibbonInnerVariableDecidableEq horizontalRibbonRoutedVariableDecidableEq
set_option maxHeartbeats 800000

private theorem nativeRouted_literalCount_lower (source : PeriodicCNF Nat) :
    (horizontalFormula source).erase.presentationLiteralCount ≤
      (horizontalRoutedFormulaComputed source).erase.presentationLiteralCount := by
  rw [horizontalRoutedFormulaComputed_eq_semanticData, horizontalSemanticRoutedFormula, erase_formula,
    PeriodicCNF.literalCount_variableGauge]
  have bound := PeriodicOneInThreePolarityNormalization.literalCount_le
    (refinedSource (horizontalFormula source) (horizontalPlacement source)).erase
  simpa only [refinedSource, PositionedPeriodicCNF.erase_scale, PositionedPeriodicCNF.erase_anchorNormalize,
    PeriodicCNF.literalCount_anchorNormalize] using bound

private theorem nativeRouted_source_variables_bound (source : PeriodicCNF Nat) :
    9 * (sourceFormula source).variableOccurrences.dedup.length ≤
      (horizontalRoutedFormulaComputed source).erase.presentationLiteralCount := by
  have bound := PeriodicPlanarSAT.ExactOneEndpoint.source_variables_nine_le_literals
    (sourceFormula source) (sourceFormula_isLocal source) (sourceFormula_widthAtMostThree source)
    (sourceFormula_occurrencesAtMostThree_canonicalBEq source) (sourceFormula_clausesNonempty source)
  rw [PeriodicPlanarSAT.ExactOneEndpoint.positioned,
    PeriodicOrthocrossing.retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormulaComputed_eq
      _ (sourceFormula_isLocal source) (sourceFormula_widthAtMostThree source)
      (sourceFormula_occurrencesAtMostThree_canonicalBEq source) (sourceFormula_clausesNonempty source)] at bound
  exact bound.trans (nativeRouted_literalCount_lower source)

variable {Input : Type} {encoding : _root_.Computability.FinEncoding Input} {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)
noncomputable local instance nativeGridStackFintype (stack : decider.tm.K) : Fintype (decider.tm.Γ stack) :=
  decider.stackAlphabetFinite stack

theorem nativePlanarInput_gridBound (s : List encoding.Γ) :
    PeriodicPlanarSAT.GridBound 637009920 (nativePlanarInput decider s) := by
  let source := PeriodicCNF.PolySpaceCompiler.formulaOfSymbols decider s
  have periodBound : (horizontalRoutedPlacementComputed source).period ≤
      (3 * horizontalPlacementPeriodFactor) * (16 * (2 * (sourceFormula source).presentationSize + 1)) := by
    rw [nativeRoutedPeriod_eq]
    exact Nat.mul_le_mul_left _ (PeriodicCNF.drawingGridSize_incidenceGraph_le_presentationSize (sourceFormula source))
  norm_num [horizontalPlacementPeriodFactor] at periodBound
  have sourceBound := PeriodicCNF.presentationSize_le_variables (sourceFormula source)
    (sourceFormula_occurrencesAtMostThree_canonicalBEq source) (sourceFormula_clausesNonempty source)
  have literalBound : 9 * (sourceFormula source).variableOccurrences.dedup.length ≤
      (nativePlanarInput decider s).1.presentationLiteralCount := by
    simpa only [nativePlanarInput, nativeNormalizedFormula, PeriodicCNF.literalCount_rename,
      PeriodicCNF.literalCount_anchorNormalize, nativeRoutedFormulaSource] using nativeRouted_source_variables_bound source
  change (nativeRoutedDrawing decider s).gridSize ≤ 637009920 * ((nativePlanarInput decider s).1.presentationSize + 1)
  rw [nativeDrawingGridSize]
  unfold PeriodicCNF.presentationSize
  change (horizontalRoutedPlacementComputed source).period ≤ _
  omega

end LeanTrominoes.PeriodicCNFStripReduction
end
