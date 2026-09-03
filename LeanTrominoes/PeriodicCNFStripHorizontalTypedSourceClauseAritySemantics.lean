/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedClauseAritySemantics
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMTypedElementDegrees
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationClauseMapArity

/-! # Clause arities of the horizontal typed 3DM source -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

/-- The final padding scale and zero-anchor gauge preserve the routed
formula's clause arities, while route subdivision exposes exactly the
polarity-normalized arity sequence of the final gauged horizontal formula. -/
theorem horizontalThreeDMTypedSourceComputed_clauseLengths_eq_horizontalFormula
    (source : PeriodicCNF Nat) :
    (horizontalThreeDMTypedSourceComputed source).clauses.map List.length =
      (PeriodicOneInThreePolarityNormalization.formula
        (horizontalFormula source).erase).clauses.map List.length := by
  unfold horizontalThreeDMTypedSourceComputed
  rw [horizontalNormalizedRoutedFormulaComputed_eq_normalizedSource]
  simp only [
    PeriodicPlanarOneInThreeToThreeDM.normalizedPositionedSource,
    PositionedPeriodicCNF.erase_anchorNormalize,
    PositionedPeriodicCNF.erase_scale]
  rw [PeriodicCNF.anchorNormalize_clauseLengths]
  exact
    horizontalRoutedFormulaComputed_clauseLengths_eq_horizontalFormula
      source

end LeanTrominoes.PeriodicCNFStripReduction
