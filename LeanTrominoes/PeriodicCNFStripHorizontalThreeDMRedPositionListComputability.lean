/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMRedPositionComputability
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMEnumerationComputability

/-! # Computability of the concrete assembled red-position list -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalThreeDMTripleVariableDecidableEq

def horizontalThreeDMRedPositionsComputed
    (source : PeriodicCNF Nat) : List Cell :=
  (PeriodicPlanarOneInThreeToThreeDM.redElements
      (horizontalNormalizedRoutedFormulaComputed source).erase).map
    (horizontalThreeDMRedPositionComputed source)

theorem horizontalThreeDMRedPositionsComputed_primrec :
    Primrec horizontalThreeDMRedPositionsComputed := by
  exact Primrec.list_map
    (PeriodicPlanarOneInThreeToThreeDM.redElements_primrec.comp
      (PositionedPeriodicCNF.erase_primrec.comp
        horizontalNormalizedRoutedFormulaComputed_primrec))
    horizontalThreeDMRedPositionComputed_primrec.to₂

end PeriodicCNFStripReduction
end LeanTrominoes
