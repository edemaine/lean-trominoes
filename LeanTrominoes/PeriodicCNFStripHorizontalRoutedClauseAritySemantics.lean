/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalEncoderData
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedFormulaSemanticBridge
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivisionArity

/-! # Clause arities of the horizontal routed formula -/

set_option maxHeartbeats 800000

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

attribute [local instance]
  horizontalRoutedFormulaSourceVariableDecidableEq

/-- The computed routed formula has exactly the arity sequence emitted by
polarity normalization of the final gauged horizontal source. -/
theorem horizontalRoutedFormulaComputed_clauseLengths_eq_horizontalFormula
    (source : PeriodicCNF Nat) :
    (horizontalRoutedFormulaComputed source).erase.clauses.map List.length =
      (PeriodicOneInThreePolarityNormalization.formula
        (horizontalFormula source).erase).clauses.map List.length := by
  rw [horizontalRoutedFormulaComputed_eq_semanticData]
  simpa only [horizontalSemanticRoutedFormula] using
    PeriodicOneInThreePolarityNormalizationRouteSubdivision.formula_clauseLengths
      (horizontalFormula source)
      (horizontalPlacement source)
      (horizontalRoutes source)

end LeanTrominoes.PeriodicCNFStripReduction
