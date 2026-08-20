/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalRibbonSemanticData
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedFormulaBridge
import LeanTrominoes.PeriodicCNFStripHorizontalRoutesSemanticBridge

/-! # Semantic bridge for the horizontal routed formula -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance] sourceVariableDecidableEq

theorem horizontalRoutedFormulaComputed_eq_semanticData
    (source : PeriodicCNF Nat) :
    horizontalRoutedFormulaComputed source =
      horizontalSemanticRoutedFormula source := by
  rw [horizontalSemanticRoutedFormula,
    horizontalRoutes_eq_finalGaugedIncidenceRoutes]
  exact horizontalRoutedFormulaComputed_eq_semantic source

end PeriodicCNFStripReduction
end LeanTrominoes
