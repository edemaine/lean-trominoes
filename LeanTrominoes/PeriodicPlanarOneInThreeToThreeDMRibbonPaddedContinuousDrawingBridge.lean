/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonPaddedContinuousPresentation

/-! # Drawing projection of the padded coordinated presentation -/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

/-- Forgetting the certificates of the padded continuous presentation exposes
exactly the drawing assembled from its coordinated three-strand routing. -/
theorem paddedNormalizedCoordinatedContinuousPlanarPresentation_drawing
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement)
    (width : source.erase.WidthAtMost 3)
    (polarityNormalized :
      PeriodicOneInThreePolarityNormalization.FormulaPolarityNormalized
        source.erase)
    (occurrences : source.erase.OccurrencesAtMost 3)
    (arity : PeriodicOneInThreeNoUnits.ArityTwoOrThree source.erase)
    (variableOrdered :
      source.VariableRoutesInOccurrenceOrder presentation.routes)
    (clauseOrdered :
      source.TernaryClauseRoutesInClockwiseOrder presentation.routes) :
    (paddedNormalizedCoordinatedContinuousPlanarPresentation
      presentation width polarityNormalized occurrences arity
      variableOrdered clauseOrdered).drawing =
      assembledDrawing
        (paddedNormalizedCoordinatedRibbonThreeStrandRouting
          presentation width occurrences arity variableOrdered clauseOrdered) := by
  rfl

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
