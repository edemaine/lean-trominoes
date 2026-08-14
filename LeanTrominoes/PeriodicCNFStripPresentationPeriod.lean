/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalProblem
import LeanTrominoes.PeriodicCNFStripHorizontalPeriodSize
import LeanTrominoes.PeriodicCNFPlanarRetainedPolarityNormalizedRibbonThreeDMPeriod

/-!
# Grid period of the concrete planar 3DM presentation
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance] sourceVariableDecidableEq

/-- Polarity route subdivision, vertical padding, and the fixed three-strand
layout are the only remaining period refinements after the horizontal
exact-one placement. -/
theorem presentation_drawing_gridSize_eq (source : PeriodicCNF Nat) :
    (presentation source).drawing.gridSize =
      PeriodicPlanarOneInThreeToThreeDM.standardThreeStrandLayout.factor *
        (2 *
          (PeriodicOneInThreePolarityNormalizationRouteSubdivision.refinementFactor *
            (horizontalPlacement source).period)) := by
  exact
    PeriodicOrthocrossing.retainedOrderedFixedEightPolarityNormalizedPaddedContinuousPlanarPresentation_drawing_gridSize
      (sourceFormula source)
      (sourceFormula_isLocal source)
      (sourceFormula_widthAtMostThree source)
      (sourceFormula_occurrencesAtMostThree_canonicalBEq source)
      (sourceFormula_clausesNonempty source)

end PeriodicCNFStripReduction
end LeanTrominoes
