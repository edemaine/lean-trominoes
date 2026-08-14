/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalRoutedFormulaComputability

/-! # Bridge from the executable routed formula to the retained semantic term -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalRoutedFormulaSourceVariableDecidableEq

/-- The executable routed formula is exactly the retained routed-polarity
formula with the concrete source promises supplied. -/
theorem horizontalRoutedFormulaComputed_eq_semantic
    (source : PeriodicCNF Nat) :
    horizontalRoutedFormulaComputed source =
      PeriodicOneInThreePolarityNormalizationRouteSubdivision.formula
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
  unfold horizontalRoutedFormulaComputed
  exact
    PeriodicOrthocrossing.retainedOrderedFixedEightPolarityNormalizedPositionedFormulaComputed_eq
      (sourceFormula source)
      (sourceFormula_isLocal source)
      (sourceFormula_widthAtMostThree source)
      (sourceFormula_occurrencesAtMostThree_canonicalBEq source)
      (sourceFormula_clausesNonempty source)

end PeriodicCNFStripReduction
end LeanTrominoes
