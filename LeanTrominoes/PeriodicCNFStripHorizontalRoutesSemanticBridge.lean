/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalEncoderData
import LeanTrominoes.PeriodicCNFStripHorizontalRibbonInstances
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalGaugedRoutesProjection

/-! # Horizontal presentation-route bridge -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  sourceVariableDecidableEq
  horizontalRibbonInnerVariableDecidableEq

/-- The named horizontal routes are the canonical route field of the final
gauged retained presentation. -/
theorem horizontalRoutes_eq_finalGaugedIncidenceRoutes
    (source : PeriodicCNF Nat) :
    horizontalRoutes source =
      PeriodicOrthocrossing.retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceRoutes
        (sourceFormula source)
        (sourceFormula_isLocal source)
        (sourceFormula_widthAtMostThree source)
        (sourceFormula_occurrencesAtMostThree_canonicalBEq source)
        (sourceFormula_clausesNonempty source) := by
  unfold horizontalRoutes
  exact
    PeriodicOrthocrossing.retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedClockwiseOrderedPresentation_routes
      (sourceFormula source)
      (sourceFormula_isLocal source)
      (sourceFormula_widthAtMostThree source)
      (sourceFormula_occurrencesAtMostThree_canonicalBEq source)
      (sourceFormula_clausesNonempty source)

end PeriodicCNFStripReduction
end LeanTrominoes
