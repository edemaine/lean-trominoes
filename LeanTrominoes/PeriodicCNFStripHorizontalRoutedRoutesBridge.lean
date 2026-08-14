/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedRoutesData

/-! # Bridge from executable routed incidences to their semantic term -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq

/-- The executable routed incidence family is exactly the retained
routed-polarity family with the concrete source promises supplied. -/
theorem horizontalRoutedRoutesComputed_eq_semantic
    (source : PeriodicCNF Nat) :
    horizontalRoutedRoutesComputed source =
      PeriodicOneInThreePolarityNormalizationRouteSubdivision.incidenceRoutes
        (PeriodicOrthocrossing.retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
          (sourceFormula source)
          (sourceFormula_isLocal source)
          (sourceFormula_widthAtMostThree source)
          (sourceFormula_occurrencesAtMostThree_canonicalBEq source)
          (sourceFormula_clausesNonempty source))
        (PeriodicOrthocrossing.retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
          (sourceFormula source))
        (PeriodicOrthocrossing.retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceRoutes
          (sourceFormula source)
          (sourceFormula_isLocal source)
          (sourceFormula_widthAtMostThree source)
          (sourceFormula_occurrencesAtMostThree_canonicalBEq source)
          (sourceFormula_clausesNonempty source)) := by
  unfold horizontalRoutedRoutesComputed
  exact
    PeriodicOrthocrossing.retainedOrderedFixedEightPolarityNormalizedIncidenceRoutesComputed_eq
      (sourceFormula source)
      (sourceFormula_isLocal source)
      (sourceFormula_widthAtMostThree source)
      (sourceFormula_occurrencesAtMostThree_canonicalBEq source)
      (sourceFormula_clausesNonempty source)

end PeriodicCNFStripReduction
end LeanTrominoes
