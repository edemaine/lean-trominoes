/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FixedPlanarThreeDMSeedCompleteness
import LeanTrominoes.PeriodicThreeDMNormalizationVertexSeparation
import LeanTrominoes.PeriodicThreeDMNormalizationWellFormed

/-! # Geometry certificates for the fixed seeded planar 3DM problem -/
noncomputable section
set_option synthInstance.maxSize 2048
namespace LeanTrominoes.FixedPlanarThreeDMSeed
open PeriodicOrthocrossing

private theorem cast_drawing {p q : PeriodicThreeDM} (equal : p = q)
    (presentation : q.ContinuousPlanarPresentation) :
    (equal.symm ▸ presentation).drawing = presentation.drawing := by
  cases equal
  rfl

private theorem fixedPresentation_drawing : fixedPresentation.drawing =
    (retainedOrderedFixedEightPolarityNormalizedPaddedContinuousPlanarPresentation source
      FixedThreeSATThreeSeed.fixedFormula_isLocal
      FixedThreeSATThreeSeed.fixedFormula_widthAtMostThree source_occurrences
      FixedThreeSATThreeSeed.fixedFormula_clausesNonempty).drawing :=
  cast_drawing fixedInstance_eq _

theorem fixedInstance_degree : fixedInstance.DegreeTwoOrThree := by
  rw [fixedInstance_eq]
  exact retainedOrderedFixedEightPolarityNormalizedPaddedPeriodicThreeDMProblem_degreeTwoOrThree
    source FixedThreeSATThreeSeed.fixedFormula_isLocal
    FixedThreeSATThreeSeed.fixedFormula_widthAtMostThree source_occurrences
    FixedThreeSATThreeSeed.fixedFormula_clausesNonempty

theorem fixedPresentation_separated : fixedPresentation.drawing.LiftedRoutesAvoidEachOther := by
  rw [fixedPresentation_drawing]
  exact retainedOrderedFixedEightPolarityNormalizedPaddedContinuousPlanarPresentation_separated
    source FixedThreeSATThreeSeed.fixedFormula_isLocal
    FixedThreeSATThreeSeed.fixedFormula_widthAtMostThree source_occurrences
    FixedThreeSATThreeSeed.fixedFormula_clausesNonempty

theorem fixedPresentation_routesSimple : ∀ route ∈ fixedPresentation.drawing.edgeRoutes,
    LocalIncidenceDrawing.RouteIsSimple route := by
  rw [fixedPresentation_drawing]
  exact retainedOrderedFixedEightPolarityNormalizedPaddedContinuousPlanarPresentation_routesSimple
    source FixedThreeSATThreeSeed.fixedFormula_isLocal
    FixedThreeSATThreeSeed.fixedFormula_widthAtMostThree source_occurrences
    FixedThreeSATThreeSeed.fixedFormula_clausesNonempty

theorem fixedPresentation_collisionFree :
    fixedPresentation.toPlanarPresentation.FinalAssignmentsCollisionFree :=
  fixedPresentation.finalAssignmentsCollisionFree fixedPresentation.problemWellFormed
    fixedInstance_degree fixedPresentation_separated fixedPresentation_routesSimple

theorem fixedDrawing_wellFormed :
    fixedPresentation.toPlanarPresentation.normalizedOrthogonalDrawing.IsWellFormed :=
  fixedPresentation.normalizedOrthogonalDrawing_isWellFormed fixedPresentation.problemWellFormed
    fixedInstance_degree fixedPresentation_separated fixedPresentation_routesSimple

theorem fixedDrawing_verticesSeparated :
    fixedPresentation.toPlanarPresentation.normalizedOrthogonalDrawing.VerticesSeparated :=
  fixedPresentation.toPlanarPresentation.normalizedOrthogonalDrawing_verticesSeparated

end LeanTrominoes.FixedPlanarThreeDMSeed
