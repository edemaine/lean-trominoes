/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedPlacementData

/-! # Bridge from the executable routed placement to its semantic term -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalRoutedPlacementSourceVariableDecidableEq

/-- The executable routed placement is exactly the retained routed-polarity
placement with the concrete source promises supplied. -/
theorem horizontalRoutedPlacementComputed_eq_semantic
    (source : PeriodicCNF Nat) :
    horizontalRoutedPlacementComputed source =
      PeriodicOneInThreePolarityNormalizationRouteSubdivision.placement
        (PeriodicOrthocrossing.retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
          (sourceFormula source))
        (PeriodicOrthocrossing.retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceRoutes
          (sourceFormula source)
          (sourceFormula_isLocal source)
          (sourceFormula_widthAtMostThree source)
          (sourceFormula_occurrencesAtMostThree_canonicalBEq source)
          (sourceFormula_clausesNonempty source)) := by
  unfold horizontalRoutedPlacementComputed
  exact
    PeriodicOrthocrossing.retainedOrderedFixedEightPolarityNormalizedPlacementComputed_eq
      (sourceFormula source)
      (sourceFormula_isLocal source)
      (sourceFormula_widthAtMostThree source)
      (sourceFormula_occurrencesAtMostThree_canonicalBEq source)
      (sourceFormula_clausesNonempty source)

end PeriodicCNFStripReduction
end LeanTrominoes
