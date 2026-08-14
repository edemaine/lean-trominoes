/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMGreenPositionComputability
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMEnumerationComputability

/-! # Computability of the concrete assembled green-position list -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalThreeDMTripleVariableDecidableEq

def horizontalThreeDMGreenPositionsComputed
    (source : PeriodicCNF Nat) : List Cell :=
  (PeriodicPlanarOneInThreeToThreeDM.greenElements
      (horizontalNormalizedRoutedFormulaComputed source).erase).map
    (horizontalThreeDMGreenPositionComputed source)

theorem horizontalThreeDMGreenPositionsComputed_primrec :
    Primrec horizontalThreeDMGreenPositionsComputed := by
  exact Primrec.list_map
    (PeriodicPlanarOneInThreeToThreeDM.greenElements_primrec.comp
      (PositionedPeriodicCNF.erase_primrec.comp
        horizontalNormalizedRoutedFormulaComputed_primrec))
    horizontalThreeDMGreenPositionComputed_primrec.to₂

end PeriodicCNFStripReduction
end LeanTrominoes
