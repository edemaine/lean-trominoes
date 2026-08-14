/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMVertexPositionsData
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMGlobalVertexPositionListBridge

/-! # Identification of concrete and generic data-only vertex positions -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalThreeDMTripleVariableDecidableEq

theorem horizontalThreeDMVertexPositionsData_eq_listData
    (source : PeriodicCNF Nat) :
    horizontalThreeDMVertexPositionsData source =
      PeriodicPlanarOneInThreeToThreeDM.assembledVertexPositionListData
        (horizontalNormalizedRoutedFormulaComputed source).erase
        (horizontalThreeDMVariableOriginComputed source)
        (horizontalThreeDMClauseOriginComputed source) := by
  unfold horizontalThreeDMVertexPositionsData
    horizontalThreeDMColoredPositionsData
    horizontalThreeDMGreenBluePositionsData
    PeriodicPlanarOneInThreeToThreeDM.assembledVertexPositionListData
    PeriodicPlanarOneInThreeToThreeDM.assembledColoredElementPositionsData
    PeriodicPlanarOneInThreeToThreeDM.assembledGreenBlueElementPositionsData
  apply congrArg₂ (fun left right : List Cell => left ++ right)
  · rfl
  · apply congrArg₂ (fun left right : List Cell => left ++ right)
    · rfl
    · apply congrArg₂ (fun left right : List Cell => left ++ right)
      · rfl
      · rfl

theorem horizontalThreeDMVertexPositionsData_eq_assembled
    (source : PeriodicCNF Nat) :
    horizontalThreeDMVertexPositionsData source =
      PeriodicPlanarOneInThreeToThreeDM.assembledVertexPositionsData
        (horizontalNormalizedRoutedFormulaComputed source).erase
        (horizontalThreeDMVariableOriginComputed source)
        (horizontalThreeDMClauseOriginComputed source) := by
  exact (horizontalThreeDMVertexPositionsData_eq_listData source).trans
    (PeriodicPlanarOneInThreeToThreeDM.assembledVertexPositionListData_eq_assembled
        (horizontalNormalizedRoutedFormulaComputed source).erase
        (horizontalThreeDMVariableOriginComputed source)
        (horizontalThreeDMClauseOriginComputed source))

end PeriodicCNFStripReduction
end LeanTrominoes
