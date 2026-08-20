/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMTypedElementDegrees
import LeanTrominoes.PeriodicCNFStripHorizontalNormalizedRibbonEraseBridge
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationPresentationProperties

/-! # Clause arity of the computed horizontal 3DM source -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  sourceVariableDecidableEq
  horizontalRibbonInnerVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq
  horizontalThreeDMTripleVariableDecidableEq

theorem horizontalFormula_arityTwoOrThreeComputed
    (source : PeriodicCNF Nat) :
    PeriodicOneInThreeNoUnits.ArityTwoOrThree
      (horizontalFormula source).erase := by
  unfold horizontalFormula
  exact
    PeriodicOrthocrossing.retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula_arityTwoOrThree
      (sourceFormula source)
      (sourceFormula_isLocal source)
      (sourceFormula_widthAtMostThree source)
      (sourceFormula_occurrencesAtMostThree_canonicalBEq source)
      (sourceFormula_clausesNonempty source)

theorem horizontalSemanticRoutedFormula_arityTwoOrThreeComputed
    (source : PeriodicCNF Nat) :
    PeriodicOneInThreeNoUnits.ArityTwoOrThree
      (horizontalSemanticRoutedFormula source).erase := by
  unfold horizontalSemanticRoutedFormula
  exact
    PeriodicOneInThreePolarityNormalizationRouteSubdivision.formula_arityTwoOrThree
      (horizontalFormula source) (horizontalPlacement source)
      (horizontalRoutes source)
      (horizontalFormula_arityTwoOrThreeComputed source)

theorem horizontalThreeDMTypedSourceComputed_arityTwoOrThree
    (source : PeriodicCNF Nat) :
    PeriodicOneInThreeNoUnits.ArityTwoOrThree
      (horizontalThreeDMTypedSourceComputed source) := by
  rw [horizontalThreeDMTypedSourceComputed,
    horizontalNormalizedRoutedEraseComputed_eq_semanticData]
  change
    PeriodicOneInThreeNoUnits.ArityTwoOrThree
      (PeriodicPlanarOneInThreeToThreeDM.normalizedSource
        ((horizontalSemanticRoutedFormula source).scale 2)
        ((horizontalSemanticRoutedPlacement source).scale 2))
  apply PeriodicPlanarOneInThreeToThreeDM.normalizedSource_arityTwoOrThree
  simpa using horizontalSemanticRoutedFormula_arityTwoOrThreeComputed source

end PeriodicCNFStripReduction
end LeanTrominoes
