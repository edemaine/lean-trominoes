/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRibbonThreeDM

/-!
# Period of the polarity-normalized ribbon 3DM drawing
-/

noncomputable section

namespace LeanTrominoes
namespace PeriodicOneInThreePolarityNormalizationRouteSubdivision

/-- The generic ribbon assembly multiplies the source placement period by
the polarity-refinement, padding, and three-strand factors. -/
theorem paddedPeriodicThreeDMContinuousPlanarPresentation_drawing_gridSize
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {sourcePlacement : PeriodicVariablePlacement Variable}
    (presentation :
      PositionedPeriodicCNF.HaloBoundedRibbonReadyIncidencePresentation
        source sourcePlacement)
    (sourceUnitSteps :
      (PositionedPeriodicCNF.incidenceDrawing
        source sourcePlacement presentation.routes).HasUnitSteps)
    (sourceDistinct : source.AllAtomsNodup)
    (occurrences : source.erase.OccurrencesAtMost 3)
    (arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source.erase)
    (variableOrdered :
      source.VariableRoutesInOccurrenceOrder presentation.routes)
    (clauseOrdered :
      source.TernaryClauseRoutesInClockwiseOrder presentation.routes) :
    (paddedPeriodicThreeDMContinuousPlanarPresentation
      presentation sourceUnitSteps sourceDistinct occurrences arity
      variableOrdered clauseOrdered).drawing.gridSize =
      PeriodicPlanarOneInThreeToThreeDM.standardThreeStrandLayout.factor *
        (2 * (refinementFactor * sourcePlacement.period)) := by
  change
    (PeriodicPlanarOneInThreeToThreeDM.assembledDrawing
      (PeriodicPlanarOneInThreeToThreeDM.paddedNormalizedCoordinatedRibbonThreeStrandRouting
        _ _ _ _ _ _)).gridSize = _
  rw [PeriodicPlanarOneInThreeToThreeDM.assembledDrawing_gridSize]
  rfl

end PeriodicOneInThreePolarityNormalizationRouteSubdivision
end LeanTrominoes
