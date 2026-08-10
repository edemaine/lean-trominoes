import LeanTrominoes.PeriodicThreeDMNormalizationForwardCompatibility
import LeanTrominoes.PeriodicThreeDMNormalizationReverseElementOrientation

/-!
# Orientation equivalence for normalized periodic 3DM drawings

The forward construction and reverse extractor show that the compiled
normalized orthogonal drawing is orientable exactly when the contracted 3DM
incidence graph has a suppressed orientation, and hence exactly when the
original periodic 3DM instance is satisfiable.
-/

namespace LeanTrominoes

open Gadget
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

namespace PeriodicThreeDM

set_option maxRecDepth 2048

/-- Normalized drawing orientation is equivalent to the suppressed incidence
orientation represented by its contracted routes. -/
theorem ContinuousPlanarPresentation.normalizedOrthogonalDrawing_hasOrientation_iff_hasSuppressedOrientation
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (separated : presentation.drawing.LiftedRoutesAvoidEachOther)
    (sourceSimple :
      ∀ route ∈ presentation.drawing.edgeRoutes,
        LocalIncidenceDrawing.RouteIsSimple route) :
    presentation.toPlanarPresentation.normalizedOrthogonalDrawing.HasOrientation ↔
      problem.HasSuppressedOrientation := by
  constructor
  · rintro ⟨drawingWellFormed, orientation, valid⟩
    have collisionFree := presentation.finalAssignmentsCollisionFree
      wellFormed degree separated sourceSimple
    exact ⟨presentation.toPlanarPresentation.reverseGraphOrientation orientation,
      presentation.reverseGraphOrientation_isSuppressedOrientation
        wellFormed degree collisionFree orientation valid⟩
  · rintro ⟨values, valid⟩
    exact presentation.normalizedOrthogonalDrawing_hasOrientation
      wellFormed degree separated sourceSimple values valid

/-- The normalized drawing is orientable exactly when the original periodic
3DM instance has a perfect matching. -/
theorem ContinuousPlanarPresentation.normalizedOrthogonalDrawing_hasOrientation_iff_satisfiable
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (separated : presentation.drawing.LiftedRoutesAvoidEachOther)
    (sourceSimple :
      ∀ route ∈ presentation.drawing.edgeRoutes,
        LocalIncidenceDrawing.RouteIsSimple route) :
    presentation.toPlanarPresentation.normalizedOrthogonalDrawing.HasOrientation ↔
      problem.Satisfiable := by
  rw [presentation.normalizedOrthogonalDrawing_hasOrientation_iff_hasSuppressedOrientation
    wellFormed degree separated sourceSimple]
  exact (problem.satisfiable_iff_hasSuppressedOrientation degree).symm

end PeriodicThreeDM

end LeanTrominoes
