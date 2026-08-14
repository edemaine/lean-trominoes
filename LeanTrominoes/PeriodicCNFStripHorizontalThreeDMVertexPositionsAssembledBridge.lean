/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMVertexPositionsBridge
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMVertexPositionsDataBridge

/-! # Identification of executable and generic assembled vertex positions -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalThreeDMTripleVariableDecidableEq

theorem horizontalThreeDMVertexPositionsComputed_eq_assembled
    (source : PeriodicCNF Nat) :
    horizontalThreeDMVertexPositionsComputed source =
      PeriodicPlanarOneInThreeToThreeDM.assembledVertexPositionsData
        (horizontalNormalizedRoutedFormulaComputed source).erase
        (horizontalThreeDMVariableOriginComputed source)
        (horizontalThreeDMClauseOriginComputed source) := by
  exact (horizontalThreeDMVertexPositionsComputed_eq_data source).trans
    (horizontalThreeDMVertexPositionsData_eq_assembled source)

end PeriodicCNFStripReduction
end LeanTrominoes
