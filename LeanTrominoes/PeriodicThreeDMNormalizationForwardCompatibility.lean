/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationForwardRoutePortCompatibility

/-!
# Global compatibility of the forward normalized orientation

The finite vertex and route dispatchers are first combined for an arbitrary
listed provenance site.  Successful provenance lookup then transports that
result to an arbitrary cell of the infinite periodic lift.  Together with the
local-cell theorem, this proves that the constructed plane-wide assignment is
a valid orientation of the compiled drawing.
-/

namespace LeanTrominoes

open Gadget
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

namespace PeriodicThreeDM

set_option maxRecDepth 2048

/-- Every exposed port of every explicit translated provenance site is
compatible with its drawing-lattice neighbor. -/
theorem ContinuousPlanarPresentation.forwardDrawingOrientation_site_neighbor
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (collisionFree :
      presentation.toPlanarPresentation.FinalAssignmentsCollisionFree)
    (values : problem.GraphOrientation)
    (valid : problem.IsSuppressedOrientation values)
    {storedLocation : Cell} {site : FinalOrientationSite}
    (member :
      (storedLocation, site) ∈
        presentation.toPlanarPresentation.finalOrientationSites)
    (translate : Cell) (side : Side) (color : WireColor)
    (exposed :
      (site.cellType presentation.toPlanarPresentation).portColor side =
        some color) :
    let planar := presentation.toPlanarPresentation
    let location := reflectedLocation
      (Cell.add (site.point planar)
        (Cell.scale (planar.finalNormalizationPeriod : Int) translate))
    presentation.forwardDrawingOrientation values location side =
      !(presentation.forwardDrawingOrientation values
        (PeriodicOrthogonalDrawing.latticeNeighbor location side)
        side.opposite) := by
  dsimp only
  let planar := presentation.toPlanarPresentation
  cases site with
  | vertex vertex =>
      have vertexMember := planar.finalOrientationSite_vertex_data member
      have compatibility :=
        presentation.forwardDrawingOrientation_vertex_neighbor
          wellFormed degree collisionFree values valid vertexMember
            translate side color
              (by simpa [FinalOrientationSite.cellType] using exposed)
      simpa [FinalOrientationSite.point] using compatibility
  | route edge before current after =>
      rcases planar.finalOrientationSite_route_data member with
        ⟨edgeMember, leading, rest, routeEquation⟩
      have compatibility :=
        presentation.forwardDrawingOrientation_route_neighbor
          wellFormed degree collisionFree values valid edgeMember
            leading before current after rest routeEquation translate side color
              (by simpa [FinalOrientationSite.cellType] using exposed)
      simpa [FinalOrientationSite.point] using compatibility

/-- At an arbitrary lifted cell, every exposed forward-orientation port is
compatible with the opposite port of its lattice neighbor. -/
theorem ContinuousPlanarPresentation.forwardDrawingOrientation_neighbor
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (collisionFree :
      presentation.toPlanarPresentation.FinalAssignmentsCollisionFree)
    (values : problem.GraphOrientation)
    (valid : problem.IsSuppressedOrientation values)
    (location : Cell) (side : Side)
    (exposed :
      ((presentation.toPlanarPresentation.normalizedOrthogonalDrawing.getAt
        location).portColor side).isSome) :
    presentation.forwardDrawingOrientation values location side =
      !(presentation.forwardDrawingOrientation values
        (PeriodicOrthogonalDrawing.latticeNeighbor location side)
        side.opposite) := by
  let planar := presentation.toPlanarPresentation
  generalize lookup : planar.finalOrientationSiteAt location = found
  cases found with
  | none =>
      have blank :=
        planar.normalizedOrthogonalDrawing_getAt_eq_blank_of_site_none lookup
      rw [blank] at exposed
      simp [OrthogonalCellType.portColor] at exposed
  | some site =>
      have cellType :=
        planar.normalizedOrthogonalDrawing_getAt_eq_of_site_lookup
          collisionFree lookup
      have siteMember := List.mem_of_lookup_eq_some lookup
      have siteExposed :
          ((site.cellType planar).portColor side).isSome := by
        rw [← cellType]
        exact exposed
      generalize colorEq : (site.cellType planar).portColor side = port
        at siteExposed
      cases port with
      | none => simp at siteExposed
      | some color =>
          let translate :=
            planar.finalOrientationSiteOccurrenceTranslate location site
          have occurrence :=
            planar.reflectedLocation_eq_orientationSiteOccurrence lookup
          have locationEq :
              location =
                reflectedLocation
                  (Cell.add (site.point planar)
                    (Cell.scale (planar.finalNormalizationPeriod : Int)
                      translate)) := by
            calc
              location = reflectedLocation (reflectedLocation location) := by
                simp
              _ = reflectedLocation
                    (Cell.add (site.point planar)
                      (Cell.scale (planar.finalNormalizationPeriod : Int)
                        translate)) :=
                congrArg reflectedLocation occurrence
          rw [locationEq]
          exact presentation.forwardDrawingOrientation_site_neighbor
            wellFormed degree collisionFree values valid siteMember
              translate side color colorEq

/-- The forward construction is a valid global orientation of the compiled
normalized drawing. -/
theorem ContinuousPlanarPresentation.forwardDrawingOrientation_isOrientation
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (collisionFree :
      presentation.toPlanarPresentation.FinalAssignmentsCollisionFree)
    (values : problem.GraphOrientation)
    (valid : problem.IsSuppressedOrientation values) :
    presentation.toPlanarPresentation.normalizedOrthogonalDrawing.IsOrientation
      (presentation.forwardDrawingOrientation values) := by
  constructor
  · intro location
    exact ContinuousPlanarPresentation.forwardDrawingOrientation_local
      (presentation := presentation) wellFormed degree collisionFree
        values valid location
  · intro location side exposed
    exact ContinuousPlanarPresentation.forwardDrawingOrientation_neighbor
      (presentation := presentation) wellFormed degree collisionFree
        values valid location side exposed

/-- Any suppressed 3DM orientation induces an orientation of the normalized
periodic orthogonal drawing. -/
theorem ContinuousPlanarPresentation.normalizedOrthogonalDrawing_hasOrientation
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (wellFormed : problem.IsWellFormed)
    (degree : problem.DegreeTwoOrThree)
    (separated : presentation.drawing.LiftedRoutesAvoidEachOther)
    (sourceSimple :
      ∀ route ∈ presentation.drawing.edgeRoutes,
        LocalIncidenceDrawing.RouteIsSimple route)
    (values : problem.GraphOrientation)
    (valid : problem.IsSuppressedOrientation values) :
    presentation.toPlanarPresentation.normalizedOrthogonalDrawing.HasOrientation := by
  have collisionFree := presentation.finalAssignmentsCollisionFree
    wellFormed degree separated sourceSimple
  exact ⟨presentation.normalizedOrthogonalDrawing_isWellFormed
      wellFormed degree separated sourceSimple,
    presentation.forwardDrawingOrientation values,
    presentation.forwardDrawingOrientation_isOrientation
      wellFormed degree collisionFree values valid⟩

end PeriodicThreeDM

end LeanTrominoes
