/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicGridDrawingAffineUnitRefinement
import LeanTrominoes.PeriodicCNFIncidenceVertexCoverage
import LeanTrominoes.PeriodicThreeDMContractionContinuousPlanarity
import LeanTrominoes.PeriodicThreeDMVertexNormalizationRoutes

/-!
# Endpoint contacts before local 3DM vertex replacement

One round of degree-three vertex normalization first magnifies the complete
drawing by twelve, subdivides every route into unit steps, and translates all
points by the common template center.  Only after this stage are the local
endpoint prefixes replaced.  This module identifies that affine stage with
the executable `magnifiedUnitRoute` data and proves that it preserves
endpoint-only contacts.
-/

namespace LeanTrominoes

open DegreeThreeVertexNormalization

namespace PeriodicThreeDM

/-- The common affine/unit-refinement stage at the start of one vertex
normalization round. -/
def vertexNormalizationMagnifiedUnitDrawing
    (drawing : PeriodicGridDrawing) : PeriodicGridDrawing :=
  drawing.affineUnitRefine 12 center

@[simp]
theorem vertexNormalizationMagnifiedUnitDrawing_gridSize
    (drawing : PeriodicGridDrawing) :
    (vertexNormalizationMagnifiedUnitDrawing drawing).gridSize =
      12 * drawing.gridSize := by
  simp [vertexNormalizationMagnifiedUnitDrawing,
    PeriodicGridDrawing.affineUnitRefine]

/-- The affine stage places every old vertex at the executable normalized
vertex position. -/
theorem vertexNormalizationMagnifiedUnitDrawing_vertexPositions
    (drawing : PeriodicGridDrawing) :
    (vertexNormalizationMagnifiedUnitDrawing drawing).vertexPositions =
      drawing.vertexPositions.map normalizeVertexPosition := by
  unfold vertexNormalizationMagnifiedUnitDrawing
    PeriodicGridDrawing.affineUnitRefine
    PeriodicGridDrawing.translateCoordinates
    PeriodicGridDrawing.unitSubdivide
    PeriodicGridDrawing.scale
  simp only [List.map_map]
  apply List.map_congr_left
  intro point pointMember
  simp [normalizeVertexPosition, vertexNormalizationScale,
    Cell.add]
  constructor <;> omega

/-- The affine stage's stored routes are exactly `magnifiedUnitRoute` for
the old stored routes. -/
theorem vertexNormalizationMagnifiedUnitDrawing_edgeRoutes
    (drawing : PeriodicGridDrawing) :
    (vertexNormalizationMagnifiedUnitDrawing drawing).edgeRoutes =
      drawing.edgeRoutes.map magnifiedUnitRoute := by
  unfold vertexNormalizationMagnifiedUnitDrawing
    PeriodicGridDrawing.affineUnitRefine
    PeriodicGridDrawing.translateCoordinates
    PeriodicGridDrawing.unitSubdivide
    PeriodicGridDrawing.scale
  simp only [List.map_map]
  apply List.map_congr_left
  intro route routeMember
  change
    (AxisDirection.unitSubdividePolyline
      (scalePolyline 12 route)).map (Cell.add center) =
      magnifiedUnitRoute route
  unfold magnifiedUnitRoute
  have normalizedRoute :
      route.map normalizeVertexPosition =
        (scalePolyline 12 route).map
          (Cell.add center) := by
    unfold scalePolyline
    rw [List.map_map]
    apply List.map_congr_left
    intro point pointMember
    simp [normalizeVertexPosition, vertexNormalizationScale,
      Cell.add]
    constructor <;> omega
  rw [normalizedRoute]
  rw [AxisDirection.unitSubdividePolyline_map_add]

/-- Magnification, ordered subdivision, and the common center translation
preserve endpoint-only contacts before any local template is spliced in. -/
theorem vertexNormalizationMagnifiedUnitDrawing_routePointsMeetOnlyAtEndpoints
    (drawing : PeriodicGridDrawing)
    (ribbonReady : drawing.IsRibbonReady)
    (orthogonal : drawing.IsOrthogonal)
    (lengths :
      ∀ route ∈ drawing.edgeRoutes,
        2 ≤ route.length)
    (simple :
      ∀ route ∈ drawing.edgeRoutes,
        LocalIncidenceDrawing.RouteIsSimple route) :
    (vertexNormalizationMagnifiedUnitDrawing drawing)
      |>.RoutePointsMeetOnlyAtEndpoints := by
  exact
    PeriodicGridDrawing.routePointsMeetOnlyAtEndpoints_affineUnitRefine
      (by decide : 0 < 12)
      center drawing ribbonReady orthogonal lengths simple

/-- The contracted routes are simple as soon as their global drawing has the
endpoint-contact certificate still missing from the 3DM rasterization. -/
theorem ContinuousPlanarPresentation.contractedDrawing_routesSimple
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (degree : problem.DegreeTwoOrThree)
    (endpointContacts :
      presentation.contractedDrawing
        |>.RoutePointsMeetOnlyAtEndpoints) :
    ∀ route ∈ presentation.contractedDrawing.edgeRoutes,
      LocalIncidenceDrawing.RouteIsSimple route := by
  exact
    PeriodicGridDrawing.routesSimple_of_globalCertificates_of_compatible_of_loopless
      problem.contractedGraph presentation.contractedDrawing
      presentation.toPlanarPresentation.contractedDrawing_isCompatible
      (contractedGraph_edgesAreLoopless problem degree)
      (presentation.contractedDrawing_isContinuouslyPlanar degree)
      endpointContacts
      presentation.toPlanarPresentation.contractedDrawing_isOrthogonal

/-- Thus, before local endpoint templates are installed, the complete first
normalization round preserves endpoint-only contacts.  All auxiliary
premises follow from the contracted drawing API; the sole geometric input is
the contracted endpoint-contact certificate. -/
theorem ContinuousPlanarPresentation.vertexNormalizationMagnifiedUnitDrawing_contractedDrawing_routePointsMeetOnlyAtEndpoints
    {problem : PeriodicThreeDM}
    (presentation : problem.ContinuousPlanarPresentation)
    (degree : problem.DegreeTwoOrThree)
    (endpointContacts :
      presentation.contractedDrawing
        |>.RoutePointsMeetOnlyAtEndpoints) :
    (vertexNormalizationMagnifiedUnitDrawing
      presentation.contractedDrawing)
        |>.RoutePointsMeetOnlyAtEndpoints := by
  apply
    vertexNormalizationMagnifiedUnitDrawing_routePointsMeetOnlyAtEndpoints
      presentation.contractedDrawing
      ⟨presentation.contractedDrawing_isContinuouslyPlanar degree,
        endpointContacts⟩
      presentation.toPlanarPresentation.contractedDrawing_isOrthogonal
  · exact
      fun route routeMember =>
        PeriodicGridDrawing.route_length_ge_two_of_compatible_of_loopless
          problem.contractedGraph presentation.contractedDrawing
          presentation.toPlanarPresentation.contractedDrawing_isCompatible
          (contractedGraph_edgesAreLoopless problem degree)
          routeMember
  · exact presentation.contractedDrawing_routesSimple degree endpointContacts

end PeriodicThreeDM
end LeanTrominoes
