/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFStripHorizontalNormalizedRibbonSourceBridge
import LeanTrominoes.PositionedPeriodicCNFAnchorNormalizationDrawing

/-! # Normalized variable fans retain the horizontal atom presentation -/

namespace LeanTrominoes.PeriodicCNFStripReduction

/-- Padding and clause-anchor normalization preserve every atom and its
position in the horizontal occurrence stream. -/
theorem horizontalSemanticNormalizedRibbonSource_variableOccurrences
    (source : PeriodicCNF Nat) :
    (horizontalSemanticNormalizedRibbonSource source).erase.variableOccurrences =
      (horizontalRoutedFormulaComputed source).erase.variableOccurrences := by
  unfold horizontalSemanticNormalizedRibbonSource
    PeriodicPlanarOneInThreeToThreeDM.normalizedPositionedSource
  rw [PositionedPeriodicCNF.erase_anchorNormalize, PeriodicCNF.variableOccurrences_anchorNormalize,
    PositionedPeriodicCNF.erase_scale, horizontalRoutedFormulaComputed_eq_semanticData]

end LeanTrominoes.PeriodicCNFStripReduction
