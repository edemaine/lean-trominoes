/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMClauseOriginComputability
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMRedPositionData
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMGlobalRedPositionComputability

/-! # Computability of concrete assembled red-element positions -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalThreeDMTripleVariableDecidableEq

theorem horizontalThreeDMRedPositionComputed_primrec :
    Primrec fun input : PeriodicCNF Nat ×
        PeriodicPlanarOneInThreeToThreeDM.RedElement RoutedVariable =>
      horizontalThreeDMRedPositionComputed input.1 input.2 := by
  exact
    PeriodicPlanarOneInThreeToThreeDM.assembledRedElementPositionData_primrec
      (fun source : PeriodicCNF Nat =>
        (horizontalNormalizedRoutedFormulaComputed source).erase)
      horizontalThreeDMVariableOriginComputed
      horizontalThreeDMClauseOriginComputed
      (PositionedPeriodicCNF.erase_primrec.comp
        horizontalNormalizedRoutedFormulaComputed_primrec)
      horizontalThreeDMVariableOriginComputed_primrec
      horizontalThreeDMClauseOriginComputed_primrec

end PeriodicCNFStripReduction
end LeanTrominoes
