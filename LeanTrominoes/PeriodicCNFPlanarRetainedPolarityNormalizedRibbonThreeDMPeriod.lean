/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedPolarityNormalizedRibbonThreeDM
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRibbonThreeDMPeriod

/-!
# Period of the retained polarity-normalized 3DM presentation
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOrthocrossing

local instance retainedPeriodVariableDecidableEq
    {Variable : Type*} [DecidableEq Variable] :
    DecidableEq
      (OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :=
  PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

theorem
    retainedOrderedFixedEightPolarityNormalizedPaddedContinuousPlanarPresentation_drawing_gridSize
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    (retainedOrderedFixedEightPolarityNormalizedPaddedContinuousPlanarPresentation
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).drawing.gridSize =
      PeriodicPlanarOneInThreeToThreeDM.standardThreeStrandLayout.factor *
        (2 *
          (PeriodicOneInThreePolarityNormalizationRouteSubdivision.refinementFactor *
            (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
              source).period)) := by
  unfold
    retainedOrderedFixedEightPolarityNormalizedPaddedContinuousPlanarPresentation
  dsimp only
  apply
    PeriodicOneInThreePolarityNormalizationRouteSubdivision.paddedPeriodicThreeDMContinuousPlanarPresentation_drawing_gridSize

end PeriodicOrthocrossing
end LeanTrominoes
