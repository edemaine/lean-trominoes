/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeDMNormalizationStripForwardRoutePortCompatibility

/-!
# Global compatibility of the forward normalized strip orientation

Finite vertex and route compatibility lift through strip provenance lookup to
every cell of the infinite rectangular-period drawing.
-/

namespace LeanTrominoes

open Gadget
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

namespace PeriodicThreeDM

set_option maxRecDepth 2048

/-- Every exposed port of every explicit translated strip provenance site is
compatible with its drawing-lattice neighbor. -/
theorem ContinuousPlanarPresentation.forwardStripDrawingOrientation_site_neighbor
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
    (valid : problem.IsSuppressedOrientation values)
    {storedLocation : Cell} {site : FinalOrientationSite}
    (member :
      (storedLocation, site) ∈
        presentation.toPlanarPresentation.finalStripOrientationSites)
    (translate : Cell) (side : Side) (color : WireColor)
    (exposed :
      (site.cellType presentation.toPlanarPresentation).portColor side =
        some color) :
    let planar := presentation.toPlanarPresentation
    let location := Cell.add
      (stripReflectedLocation planar.finalNormalizationPeriod
        (site.point planar))
      (planar.stripPeriodTranslation translate)
    presentation.forwardStripDrawingOrientation values location side =
      !(presentation.forwardStripDrawingOrientation values
        (PeriodicOrthogonalDrawing.latticeNeighbor location side)
        side.opposite) := by
  dsimp only
  let planar := presentation.toPlanarPresentation
  rcases planar.exists_finalOrientationSite_of_mem_finalStripOrientationSites
      member with ⟨squareLocation, squareMember⟩
  cases site with
  | vertex vertex =>
      have vertexMember := planar.finalOrientationSite_vertex_data squareMember
      have compatibility :=
        presentation.forwardStripDrawingOrientation_vertex_neighbor
          wellFormed degree horizontal sourceInside collisionFree values valid
            vertexMember translate side color
              (by simpa [FinalOrientationSite.cellType] using exposed)
      simpa [FinalOrientationSite.point] using compatibility
  | route edge before current after =>
      rcases planar.finalOrientationSite_route_data squareMember with
        ⟨edgeMember, leading, rest, routeEquation⟩
      have compatibility :=
        presentation.forwardStripDrawingOrientation_route_neighbor
          wellFormed degree horizontal sourceInside collisionFree values valid
            edgeMember leading before current after rest routeEquation translate
              side color
                (by simpa [FinalOrientationSite.cellType] using exposed)
      simpa [FinalOrientationSite.point] using compatibility

/-- At an arbitrary lifted strip cell, every exposed forward-orientation port
is compatible with the opposite port of its lattice neighbor. -/
theorem ContinuousPlanarPresentation.forwardStripDrawingOrientation_neighbor
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
    (valid : problem.IsSuppressedOrientation values)
    (location : Cell) (side : Side)
    (exposed :
      ((presentation.toPlanarPresentation.stripNormalizedOrthogonalDrawing.getAt
        location).portColor side).isSome) :
    presentation.forwardStripDrawingOrientation values location side =
      !(presentation.forwardStripDrawingOrientation values
        (PeriodicOrthogonalDrawing.latticeNeighbor location side)
        side.opposite) := by
  let planar := presentation.toPlanarPresentation
  generalize lookup : planar.finalStripOrientationSiteAt location = found
  cases found with
  | none =>
      have blank :=
        planar.stripNormalizedOrthogonalDrawing_getAt_eq_blank_of_site_none
          lookup
      rw [blank] at exposed
      simp [OrthogonalCellType.portColor] at exposed
  | some site =>
      have cellType :=
        planar.stripNormalizedOrthogonalDrawing_getAt_eq_of_site_lookup
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
            planar.finalStripOrientationSiteOccurrenceTranslate location site
          have locationEq :=
            presentation.location_eq_stripOrientationSiteOccurrence
              wellFormed degree horizontal sourceInside lookup
          rw [locationEq]
          exact presentation.forwardStripDrawingOrientation_site_neighbor
            wellFormed degree horizontal sourceInside collisionFree values valid
              siteMember translate side color colorEq

end PeriodicThreeDM

end LeanTrominoes
