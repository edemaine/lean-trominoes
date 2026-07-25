import LeanTrominoes.PeriodicThreeDMContractionDrawing
import LeanTrominoes.PeriodicOrthocrossingOrthogonal

/-!
# Geometric invariants of periodic 3DM contraction

Concatenating the two routes at a suppressed degree-two element introduces
no new geometric segment.  The second route is merely translated and
traversed backward.  This file first packages orthogonality route-by-route
and then proves that the compatible contracted drawing remains orthogonal.
-/

namespace LeanTrominoes

open Gadget
open PeriodicOrthocrossing

/-- Axis alignment is unchanged when the endpoints of a segment are
swapped. -/
theorem GridSegment.isAxisAligned_swap (first second : Cell) :
    (GridSegment.mk first second).IsAxisAligned ↔
      (GridSegment.mk second first).IsAxisAligned := by
  constructor
  · rintro (⟨same, different⟩ | ⟨same, different⟩)
    · exact Or.inl ⟨same.symm, different.symm⟩
    · exact Or.inr ⟨same.symm, different.symm⟩
  · rintro (⟨same, different⟩ | ⟨same, different⟩)
    · exact Or.inl ⟨same.symm, different.symm⟩
    · exact Or.inr ⟨same.symm, different.symm⟩

/-- Translating every point preserves orthogonality of a polyline. -/
theorem PeriodicOrthocrossing.OrthogonalPolyline.translate
    {points : List Cell}
    (orthogonal : OrthogonalPolyline points)
    (offset : Cell) :
    OrthogonalPolyline (translatePolyline offset points) := by
  unfold OrthogonalPolyline translatePolyline
  apply List.isChain_map_of_isChain
    (Cell.add offset)
  · intro first second aligned
    exact
      (GridSegment.isAxisAligned_translate
        (GridSegment.mk first second) offset).2 aligned
  · exact orthogonal

/-- Traversing an orthogonal polyline backward preserves orthogonality. -/
theorem PeriodicOrthocrossing.OrthogonalPolyline.reverse
    {points : List Cell}
    (orthogonal : OrthogonalPolyline points) :
    OrthogonalPolyline points.reverse := by
  unfold OrthogonalPolyline at orthogonal ⊢
  rw [List.isChain_reverse]
  exact orthogonal.imp fun first second aligned =>
    (GridSegment.isAxisAligned_swap first second).mp aligned

/-- The indexed-segment definition of drawing orthogonality is equivalent
to checking every route as an orthogonal polyline. -/
theorem PeriodicGridDrawing.isOrthogonal_iff_routes
    (drawing : PeriodicGridDrawing) :
    drawing.IsOrthogonal ↔
      ∀ route ∈ drawing.edgeRoutes,
        OrthogonalPolyline route := by
  constructor
  · intro orthogonal route routeMem
    apply (orthogonalPolyline_iff_segments route).2
    intro segment segmentMem
    rcases List.mem_iff_getElem.mp routeMem with
      ⟨routeIndex, routeIndexLt, routeAt⟩
    rcases List.mem_iff_getElem.mp segmentMem with
      ⟨segmentIndex, segmentIndexLt, segmentAt⟩
    have taggedRouteMem :
        (route, routeIndex) ∈ drawing.edgeRoutes.zipIdx := by
      rw [List.mem_zipIdx_iff_getElem?,
        List.getElem?_eq_some_iff]
      exact ⟨routeIndexLt, routeAt⟩
    have taggedSegmentMem :
        (segment, segmentIndex) ∈
          (gridPolylineSegments route).zipIdx := by
      rw [List.mem_zipIdx_iff_getElem?,
        List.getElem?_eq_some_iff]
      exact ⟨segmentIndexLt, segmentAt⟩
    apply orthogonal
      ⟨routeIndex, segmentIndex, segment⟩
    unfold PeriodicGridDrawing.indexedSegments
    apply List.mem_flatMap.mpr
    refine ⟨(route, routeIndex), taggedRouteMem, ?_⟩
    apply List.mem_map.mpr
    exact
      ⟨(segment, segmentIndex), taggedSegmentMem, rfl⟩
  · intro routes indexed indexedMem
    unfold PeriodicGridDrawing.indexedSegments at indexedMem
    rcases List.mem_flatMap.mp indexedMem with
      ⟨taggedRoute, taggedRouteMem, indexedMem⟩
    rcases List.mem_map.mp indexedMem with
      ⟨taggedSegment, taggedSegmentMem, indexedEq⟩
    subst indexed
    exact
      (orthogonalPolyline_iff_segments taggedRoute.1).1
        (routes taggedRoute.1
          (List.fst_mem_of_mem_zipIdx taggedRouteMem))
        taggedSegment.1
        (List.fst_mem_of_mem_zipIdx taggedSegmentMem)

namespace PeriodicThreeDM

/-- Every genuine incidence route occurs in the original drawing's route
list at the tag's stable index. -/
theorem PlanarPresentation.incidenceRoute_mem
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {tag : IncidenceTag}
    (member : tag ∈ problem.incidenceTags) :
    presentation.incidenceRoute tag ∈
      presentation.drawing.edgeRoutes := by
  have tagIndexLt :
      problem.incidenceRouteIndex tag <
        problem.incidenceTags.length :=
    List.idxOf_lt_length_iff.mpr member
  have routeIndexLt :
      problem.incidenceRouteIndex tag <
        presentation.drawing.edgeRoutes.length := by
    rw [presentation.compatible.2.2.1,
      incidenceGraph_edges_length]
    exact tagIndexLt
  unfold PlanarPresentation.incidenceRoute
    PeriodicGridDrawing.edgeRoute
  rw [List.getD_eq_getElem _ _ routeIndexLt]
  exact List.getElem_mem routeIndexLt

/-- Every genuine incidence route is an orthogonal polyline. -/
theorem PlanarPresentation.incidenceRoute_orthogonal
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {tag : IncidenceTag}
    (member : tag ∈ problem.incidenceTags) :
    OrthogonalPolyline
      (presentation.incidenceRoute tag) := by
  exact
    (PeriodicGridDrawing.isOrthogonal_iff_routes
      presentation.drawing).1 presentation.orthogonal
      (presentation.incidenceRoute tag)
      (presentation.incidenceRoute_mem member)

/-- Every contracted edge route is orthogonal. -/
theorem PlanarPresentation.contractedEdgeRoute_orthogonal
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (color : WireColor) (atom : Nat)
    {edge : ContractedEdge}
    (member :
      edge ∈ problem.contractedEdgesForElement color atom) :
    OrthogonalPolyline
      (presentation.contractedEdgeRoute edge) := by
  have metadata :=
    contractedEdgesForElement_metadata
      problem color atom member
  have incidenceMembers :=
    contractedEdgesForElement_incidence_members
      problem color atom member
  cases edge with
  | retained edgeColor edgeAtom incidence =>
      simp only [ContractedEdge.color,
        ContractedEdge.atom] at metadata
      rcases metadata with ⟨rfl, rfl⟩
      have incidenceMember :
          incidence ∈ problem.incidences edgeColor edgeAtom := by
        simpa [ContractedEdge.sourceIncidence] using
          incidenceMembers.1
      exact
        presentation.incidenceRoute_orthogonal
          (incidenceTag_mem_of_incidence_mem
            problem edgeColor edgeAtom incidenceMember)
  | through edgeColor edgeAtom first second =>
      simp only [ContractedEdge.color,
        ContractedEdge.atom] at metadata
      rcases metadata with ⟨rfl, rfl⟩
      have firstMember :
          first ∈ problem.incidences edgeColor edgeAtom := by
        simpa [ContractedEdge.sourceIncidence] using
          incidenceMembers.1
      have secondMember :
          second ∈ problem.incidences edgeColor edgeAtom := by
        simpa [ContractedEdge.targetIncidence] using
          incidenceMembers.2.1
      have firstOrthogonal :=
        presentation.incidenceRoute_orthogonal
          (incidenceTag_mem_of_incidence_mem
            problem edgeColor edgeAtom firstMember)
      have secondOrthogonal :=
        presentation.incidenceRoute_orthogonal
          (incidenceTag_mem_of_incidence_mem
            problem edgeColor edgeAtom secondMember)
      have firstEndpoints :=
        presentation.incidenceRoute_endpoints_of_incidence
          edgeColor edgeAtom firstMember
      have secondEndpoints :=
        presentation.incidenceRoute_endpoints_of_incidence
          edgeColor edgeAtom secondMember
      let translate :=
        presentation.drawing.periodTranslation
          (Cell.sub first.offset second.offset)
      let reversedSecond :=
        (translatePolyline translate
          (presentation.incidenceRoute
            ⟨second.tripleIndex, edgeColor⟩)).reverse
      have reversedOrthogonal :
          OrthogonalPolyline reversedSecond :=
        (secondOrthogonal.translate translate).reverse
      have boundary :
          (presentation.incidenceRoute
              ⟨first.tripleIndex, edgeColor⟩).getLast? =
            reversedSecond.head? := by
        rw [firstEndpoints.2]
        simp only [reversedSecond, List.head?_reverse,
          translatePolyline, List.getLast?_map,
          secondEndpoints.2, Option.map_some]
        simpa [translate] using
          congrArg some
            (periodTranslation_element_endpoint_sub
              presentation.drawing
              (presentation.drawing.vertexPosition
                problem.incidenceGraph
                (.element edgeColor edgeAtom))
              first.offset second.offset).symm
      unfold PlanarPresentation.contractedEdgeRoute
      apply isChain_joinPolylines
      · exact firstOrthogonal
      · simpa [reversedSecond, translate,
          PlanarPresentation.reversedIncidenceRouteAt,
          OrthogonalPolyline] using
          reversedOrthogonal
      · simpa [reversedSecond, translate,
          PlanarPresentation.reversedIncidenceRouteAt] using boundary

/-- Contracting degree-two elements preserves orthogonality of the complete
periodic drawing. -/
theorem PlanarPresentation.contractedDrawing_isOrthogonal
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation) :
    presentation.contractedDrawing.IsOrthogonal := by
  apply
    (PeriodicGridDrawing.isOrthogonal_iff_routes
      presentation.contractedDrawing).2
  intro route routeMem
  simp only [PlanarPresentation.contractedDrawing,
    List.mem_map] at routeMem
  rcases routeMem with
    ⟨taggedEdge, taggedEdgeMem, rfl⟩
  have edgeMem :
      taggedEdge.1 ∈ problem.contractedEdges :=
    List.fst_mem_of_mem_zipIdx taggedEdgeMem
  simp only [contractedEdges,
    List.mem_flatMap] at edgeMem
  rcases edgeMem with ⟨color, colorMem, edgeMem⟩
  simp only [contractedEdgesForColor,
    List.mem_flatMap] at edgeMem
  rcases edgeMem with ⟨atom, atomMem, edgeMem⟩
  exact
    presentation.contractedEdgeRoute_orthogonal
      color atom edgeMem

end PeriodicThreeDM

end LeanTrominoes
