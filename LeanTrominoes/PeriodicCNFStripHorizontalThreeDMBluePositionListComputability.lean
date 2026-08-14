/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMBluePositionComputability
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMEnumerationComputability

/-! # Computability of the concrete assembled blue-position list -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalThreeDMTripleVariableDecidableEq

def horizontalThreeDMBluePositionsComputed
    (source : PeriodicCNF Nat) : List Cell :=
  (PeriodicPlanarOneInThreeToThreeDM.blueElements
      (horizontalNormalizedRoutedFormulaComputed source).erase).map
    (horizontalThreeDMBluePositionComputed source)

theorem horizontalThreeDMBluePositionsComputed_primrec :
    Primrec horizontalThreeDMBluePositionsComputed := by
  exact Primrec.list_map
    (PeriodicPlanarOneInThreeToThreeDM.blueElements_primrec.comp
      (PositionedPeriodicCNF.erase_primrec.comp
        horizontalNormalizedRoutedFormulaComputed_primrec))
    horizontalThreeDMBluePositionComputed_primrec.to₂

end PeriodicCNFStripReduction
end LeanTrominoes
