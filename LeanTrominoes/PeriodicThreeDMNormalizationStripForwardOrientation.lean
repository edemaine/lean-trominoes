/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationForwardOrientation
import LeanTrominoes.PeriodicThreeDMNormalizationStripOrientationSiteTransfer

/-!
# Forward local orientation on the normalized 3DM strip
-/

namespace LeanTrominoes

open Gadget

namespace PeriodicThreeDM

/-- Plane-wide strip orientation induced by a suppressed 3DM orientation.
Blank cells and unused sides receive an irrelevant `false` value. -/
noncomputable def ContinuousPlanarPresentation.forwardStripDrawingOrientation
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (values : problem.GraphOrientation) :
    presentation.toPlanarPresentation.stripNormalizedOrthogonalDrawing.Orientation :=
  fun location side =>
    let planar := presentation.toPlanarPresentation
    match planar.finalStripOrientationSiteAt location with
    | none => false
    | some site =>
        site.inward planar values
          (planar.finalStripOrientationSiteOccurrenceTranslate location site) side

/-- The forward strip orientation satisfies every local cell constraint. -/
theorem ContinuousPlanarPresentation.forwardStripDrawingOrientation_local
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (collisionFree :
      presentation.toPlanarPresentation.FinalStripAssignmentsCollisionFree)
    (values : problem.GraphOrientation)
    (valid : problem.IsSuppressedOrientation values)
    (location : Cell) :
    PeriodicOrthogonalDrawing.satisfiesOrientation
      (presentation.toPlanarPresentation.stripNormalizedOrthogonalDrawing.getAt
        location)
      (presentation.forwardStripDrawingOrientation values location) := by
  let planar := presentation.toPlanarPresentation
  generalize lookup : planar.finalStripOrientationSiteAt location = found
  cases found with
  | none =>
      have blank :=
        planar.stripNormalizedOrthogonalDrawing_getAt_eq_blank_of_site_none lookup
      rw [blank]
      simp [PeriodicOrthogonalDrawing.satisfiesOrientation]
  | some site =>
      have cellType :=
        planar.stripNormalizedOrthogonalDrawing_getAt_eq_of_site_lookup
          collisionFree lookup
      rw [cellType]
      have orientationEq :
          presentation.forwardStripDrawingOrientation values location =
            site.inward planar values
              (planar.finalStripOrientationSiteOccurrenceTranslate
                location site) := by
        funext side
        unfold ContinuousPlanarPresentation.forwardStripDrawingOrientation
        dsimp only
        rw [lookup]
      rw [orientationEq]
      have stripMember := List.mem_of_lookup_eq_some lookup
      rcases planar.exists_finalOrientationSite_of_mem_finalStripOrientationSites
          stripMember with
        ⟨squareLocation, squareMember⟩
      exact presentation.finalOrientationSite_satisfiesOrientation
        wellFormed degree values valid squareMember
          (planar.finalStripOrientationSiteOccurrenceTranslate location site)

end PeriodicThreeDM
end LeanTrominoes
