/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicGridDrawingRouteSimplicity

/-!
# Route-family consequences of ribbon-ready incidence presentations

The metadata-indexed compatibility interface proves length and simplicity
one genuine incidence at a time.  This file lifts those facts to the
anonymous stored route list used by periodic drawing transformations.
-/

namespace LeanTrominoes
namespace PositionedPeriodicCNF

/-- Every route stored by a planar incidence presentation has at least one
segment and hence at least two listed points. -/
theorem PlanarIncidencePresentation.routes_length_ge_two
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation : PlanarIncidencePresentation source placement) :
    ∀ route ∈
        (incidenceDrawing source placement presentation.routes).edgeRoutes,
      2 ≤ route.length := by
  intro route routeMember
  change route ∈ incidenceEdgeRoutes source presentation.routes
    at routeMember
  rw [incidenceEdgeRoutes_eq_metadata_map] at routeMember
  rcases List.mem_map.mp routeMember with
    ⟨incidence, incidenceMember, routeEqual⟩
  rcases List.mem_iff_get.mp incidenceMember with
    ⟨incidenceIndex, incidenceAt⟩
  have taggedMember :
      (incidence, incidenceIndex.val) ∈
        (PeriodicCNF.incidencesWithMetadata source.erase).zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_some_iff]
    exact ⟨incidenceIndex.isLt, incidenceAt⟩
  subst route
  have segmentsNonempty :=
    presentation.route_segments_ne_nil_of_tagged taggedMember
  have segmentsPositive :
      0 <
        (gridPolylineSegments
          (presentation.routes incidence.clauseIndex
            incidence.literalIndex)).length :=
    List.length_pos_iff.mpr segmentsNonempty
  rw [gridPolylineSegments_length] at segmentsPositive
  omega

/-- Every route stored by a ribbon-ready incidence presentation is simple
in the finite route-local sense. -/
theorem HaloBoundedRibbonReadyIncidencePresentation.routesSimple
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      HaloBoundedRibbonReadyIncidencePresentation source placement) :
    ∀ route ∈
        (incidenceDrawing source placement presentation.routes).edgeRoutes,
      LocalIncidenceDrawing.RouteIsSimple route := by
  intro route routeMember
  change route ∈ incidenceEdgeRoutes source presentation.routes
    at routeMember
  rw [incidenceEdgeRoutes_eq_metadata_map] at routeMember
  rcases List.mem_map.mp routeMember with
    ⟨incidence, incidenceMember, routeEqual⟩
  rcases List.mem_iff_get.mp incidenceMember with
    ⟨incidenceIndex, incidenceAt⟩
  have taggedMember :
      (incidence, incidenceIndex.val) ∈
        (PeriodicCNF.incidencesWithMetadata source.erase).zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_some_iff]
    exact ⟨incidenceIndex.isLt, incidenceAt⟩
  subst route
  exact presentation.routeIsSimple_of_tagged taggedMember

end PositionedPeriodicCNF
end LeanTrominoes
