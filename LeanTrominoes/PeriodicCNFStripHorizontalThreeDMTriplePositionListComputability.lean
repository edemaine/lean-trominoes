/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMTriplePositionComputability
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMEnumerationComputability

/-! # Computability of the concrete assembled triple-position list -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalThreeDMTripleVariableDecidableEq

def horizontalThreeDMTriplePositionsComputed
    (source : PeriodicCNF Nat) : List Cell :=
  (PeriodicPlanarOneInThreeToThreeDM.triples
      (horizontalNormalizedRoutedFormulaComputed source).erase).map
    (horizontalThreeDMTriplePositionComputed source)

theorem horizontalThreeDMTriplePositionsComputed_primrec :
    Primrec horizontalThreeDMTriplePositionsComputed := by
  exact Primrec.list_map
    (PeriodicPlanarOneInThreeToThreeDM.triples_primrec.comp
      (PositionedPeriodicCNF.erase_primrec.comp
        horizontalNormalizedRoutedFormulaComputed_primrec))
    horizontalThreeDMTriplePositionComputed_primrec.to₂

end PeriodicCNFStripReduction
end LeanTrominoes
