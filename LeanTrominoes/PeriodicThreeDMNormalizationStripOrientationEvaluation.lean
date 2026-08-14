/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationStripForwardOrientation

/-!
# Evaluating the forward normalized 3DM strip orientation
-/

namespace LeanTrominoes

open Gadget

namespace PeriodicThreeDM

/-- Drawing-grid neighbors commute with adding a complete rectangular strip
block translation to a shifted/reflected geometric point. -/
theorem PlanarPresentation.latticeNeighbor_stripPeriodOccurrence
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (point translate : Cell) (side : Side) :
    PeriodicOrthogonalDrawing.latticeNeighbor
        (Cell.add
          (stripReflectedLocation presentation.finalNormalizationPeriod point)
          (presentation.stripPeriodTranslation translate)) side =
      Cell.add
        (stripReflectedLocation presentation.finalNormalizationPeriod
          (Cell.add point (axisDirectionOfSide side).step))
        (presentation.stripPeriodTranslation translate) := by
  rcases point with ⟨pointX, pointY⟩
  rcases translate with ⟨translateX, translateY⟩
  cases side <;>
    simp [PeriodicOrthogonalDrawing.latticeNeighbor,
      stripReflectedLocation, PlanarPresentation.stripPeriodTranslation,
      axisDirectionOfSide, AxisDirection.step, Cell.add] <;> omega

/-- At an explicit rectangular-period occurrence, the forward strip
orientation evaluates to the inward function stored by its provenance. -/
theorem ContinuousPlanarPresentation.forwardStripDrawingOrientation_periodOccurrence
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (horizontal : problem.IsOneDimensional)
    (sourceInside :
      presentation.toPlanarPresentation.drawing
        |>.RoutePointsInExpandedVerticalBand)
    (collisionFree :
      presentation.toPlanarPresentation.FinalStripAssignmentsCollisionFree)
    (values : problem.GraphOrientation)
    {storedLocation translate : Cell} {site : FinalOrientationSite}
    (member : (storedLocation, site) ∈
      presentation.toPlanarPresentation.finalStripOrientationSites)
    (side : Side) :
    let planar := presentation.toPlanarPresentation
    let location := Cell.add
      (stripReflectedLocation planar.finalNormalizationPeriod
        (site.point planar))
      (planar.stripPeriodTranslation translate)
    presentation.forwardStripDrawingOrientation values location side =
      site.inward planar values translate side := by
  dsimp only
  let planar := presentation.toPlanarPresentation
  have lookup :=
    presentation.finalStripOrientationSiteAt_periodOccurrence
      wellFormed degree horizontal sourceInside collisionFree member
      (translate := translate)
  have translateEqual :=
    presentation.finalStripOrientationSiteOccurrenceTranslate_eq
      wellFormed degree horizontal sourceInside lookup (translate := translate) rfl
  unfold ContinuousPlanarPresentation.forwardStripDrawingOrientation
  dsimp only
  rw [lookup]
  change site.inward planar values
      (planar.finalStripOrientationSiteOccurrenceTranslate
        (Cell.add
          (stripReflectedLocation planar.finalNormalizationPeriod
            (site.point planar))
          (planar.stripPeriodTranslation translate)) site) side =
    site.inward planar values translate side
  rw [translateEqual]

end PeriodicThreeDM
end LeanTrominoes
