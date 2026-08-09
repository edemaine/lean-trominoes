import LeanTrominoes.PeriodicThreeDMContractedElementDegree
import LeanTrominoes.PeriodicThreeDMContractionContinuousPlanarity

/-!
# Realized endpoint rays of the contracted drawing

For geometric normalization, an endpoint direction must be tied to the
actual first segment leaving its vertex.  At a source this is the stored
first segment.  At a target it is the reverse of the stored last segment,
translated back by the edge offset to the base occurrence of the target
vertex.  The resulting ray data retains the original indexed segment and
period translation, so continuous planarity can compare any two rays.
-/

namespace LeanTrominoes

open Gadget

namespace PeriodicThreeDM

/-- Endpoint theorem for any emitted contracted edge, independent of the
element-major block in which membership was witnessed. -/
theorem PlanarPresentation.contractedEdgeRoute_endpoints_of_mem
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {edge : ContractedEdge}
    (member : edge ∈ problem.contractedEdges) :
    (presentation.contractedEdgeRoute edge).head? =
        some (presentation.drawing.vertexPosition
          problem.incidenceGraph edge.toPeriodicEdge.source) ∧
      (presentation.contractedEdgeRoute edge).getLast? =
        some (Cell.add
          (presentation.drawing.vertexPosition
            problem.incidenceGraph edge.toPeriodicEdge.target)
          (presentation.drawing.periodTranslation
            edge.toPeriodicEdge.offset)) := by
  simp only [contractedEdges, List.mem_flatMap] at member
  rcases member with ⟨color, colorMember, member⟩
  simp only [contractedEdgesForColor, List.mem_flatMap] at member
  rcases member with ⟨atom, atomMember, member⟩
  exact presentation.contractedEdgeRoute_endpoints color atom member

/-- The named route of an emitted edge occurs at that edge's unique index
in the complete contracted drawing. -/
theorem PlanarPresentation.contractedEdgeRoute_mem_zipIdx
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    {edge : ContractedEdge}
    (member : edge ∈ problem.contractedEdges) :
    (presentation.contractedEdgeRoute edge,
        problem.contractedEdges.idxOf edge) ∈
      presentation.contractedDrawing.edgeRoutes.zipIdx := by
  have indexLt :
      problem.contractedEdges.idxOf edge <
        problem.contractedEdges.length :=
    List.idxOf_lt_length_of_mem member
  have taggedMember :
      (edge, problem.contractedEdges.idxOf edge) ∈
        problem.contractedEdges.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_some_iff]
    exact ⟨indexLt, List.getElem_idxOf indexLt⟩
  have routeIndexLt :
      problem.contractedEdges.idxOf edge <
        presentation.contractedDrawing.edgeRoutes.length := by
    simpa [PlanarPresentation.contractedDrawing] using indexLt
  have lookup := presentation.contractedDrawing_edgeRoute taggedMember
  unfold PeriodicGridDrawing.edgeRoute at lookup
  rw [List.getD_eq_getElem _ _ routeIndexLt] at lookup
  rw [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_some_iff]
  refine ⟨routeIndexLt, ?_⟩
  change presentation.contractedDrawing.edgeRoutes[
      problem.contractedEdges.idxOf edge] =
    presentation.contractedEdgeRoute edge
  exact lookup

/-- The advertised final direction of an orthogonal route is the direction
of its displayed last segment, without requiring unit length. -/
theorem AxisDirection.polylineLastDirection_append_pair_of_axisAligned
    (leading : List Cell) {before last : Cell}
    (aligned : (GridSegment.mk before last).IsAxisAligned) :
    AxisDirection.polylineLastDirection
        (leading ++ [before, last]) =
      AxisDirection.between before last := by
  unfold AxisDirection.polylineLastDirection
  simp only [List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.cons_append]
  change
    (AxisDirection.between last before).opposite =
      AxisDirection.between before last
  rw [AxisDirection.between_reverse_eq_opposite
    (AxisDirection.between_isGenuine_of_axisAligned aligned)]
  simp

/-- Negating a graph-lattice offset cancels its scaled period translation. -/
theorem add_periodTranslation_neg_offset
    (drawing : PeriodicGridDrawing) (point offset : Cell) :
    Cell.add
        (Cell.add point (drawing.periodTranslation offset))
        (drawing.periodTranslation (-offset.1, -offset.2)) =
      point := by
  rcases point with ⟨pointX, pointY⟩
  rcases offset with ⟨offsetX, offsetY⟩
  simp [PeriodicGridDrawing.periodTranslation, Cell.scale, Cell.add]

/-- One outward segment occurrence at a contracted edge endpoint. -/
structure ContractedEndpointRay
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (endpoint : ContractedEndpoint) where
  indexed : IndexedGridSegment
  indexedMember : indexed ∈ presentation.contractedDrawing.indexedSegments
  translate : Cell
  reversed : Bool
  routeIndex_eq :
    indexed.routeIndex = problem.contractedEdges.idxOf endpoint.edge
  startsAt :
    ((if reversed then indexed.segment.reverse else indexed.segment).translate
      (presentation.contractedDrawing.periodTranslation translate)).start =
        presentation.contractedDrawing.vertexPosition
          problem.contractedGraph endpoint.vertex
  direction_eq :
    AxisDirection.between
        ((if reversed then indexed.segment.reverse else indexed.segment).translate
          (presentation.contractedDrawing.periodTranslation translate)).start
        ((if reversed then indexed.segment.reverse else indexed.segment).translate
          (presentation.contractedDrawing.periodTranslation translate)).finish =
      endpoint.outwardDirection presentation

namespace ContractedEndpointRay

/-- The segment traversed outward, before placing its lifted occurrence. -/
def traversalSegment
    {problem : PeriodicThreeDM}
    {presentation : problem.PlanarPresentation}
    {endpoint : ContractedEndpoint}
    (ray : ContractedEndpointRay presentation endpoint) : GridSegment :=
  if ray.reversed then ray.indexed.segment.reverse else ray.indexed.segment

/-- Actual lifted segment traversed outward from the base vertex. -/
def realized
    {problem : PeriodicThreeDM}
    {presentation : problem.PlanarPresentation}
    {endpoint : ContractedEndpoint}
    (ray : ContractedEndpointRay presentation endpoint) : GridSegment :=
  ray.traversalSegment.translate
    (presentation.contractedDrawing.periodTranslation ray.translate)

theorem realized_start
    {problem : PeriodicThreeDM}
    {presentation : problem.PlanarPresentation}
    {endpoint : ContractedEndpoint}
    (ray : ContractedEndpointRay presentation endpoint) :
    ray.realized.start =
      presentation.contractedDrawing.vertexPosition
        problem.contractedGraph endpoint.vertex := by
  exact ray.startsAt

theorem realized_direction
    {problem : PeriodicThreeDM}
    {presentation : problem.PlanarPresentation}
    {endpoint : ContractedEndpoint}
    (ray : ContractedEndpointRay presentation endpoint) :
    AxisDirection.between ray.realized.start ray.realized.finish =
      endpoint.outwardDirection presentation := by
  exact ray.direction_eq

/-- Every endpoint ray is a genuine axis-aligned segment. -/
theorem realized_isAxisAligned
    {problem : PeriodicThreeDM}
    {presentation : problem.PlanarPresentation}
    {endpoint : ContractedEndpoint}
    (ray : ContractedEndpointRay presentation endpoint) :
    ray.realized.IsAxisAligned := by
  have original := presentation.contractedDrawing_isOrthogonal
    ray.indexed ray.indexedMember
  change
    (ray.traversalSegment.translate
      (presentation.contractedDrawing.periodTranslation ray.translate)).IsAxisAligned
  rw [GridSegment.isAxisAligned_translate]
  cases reversedEq : ray.reversed with
  | false => simpa [traversalSegment, reversedEq] using original
  | true =>
      simp only [traversalSegment, reversedEq,
        if_true, GridSegment.IsAxisAligned]
      rcases original with horizontal | vertical
      · exact Or.inl ((GridSegment.isHorizontal_reverse_iff _).2 horizontal)
      · exact Or.inr ((GridSegment.isVertical_reverse_iff _).2 vertical)

end ContractedEndpointRay

/-- Every actual edge endpoint supplies a realized outward ray. -/
theorem ContractedEndpoint.exists_ray
    {problem : PeriodicThreeDM}
    (presentation : problem.PlanarPresentation)
    (degree : problem.DegreeTwoOrThree)
    {endpoint : ContractedEndpoint}
    (member : endpoint ∈ problem.contractedEndpoints) :
    Nonempty (ContractedEndpointRay presentation endpoint) := by
  have edgeMember := endpoint.edge_mem_of_mem member
  have routeMember := presentation.contractedEdgeRoute_mem_zipIdx edgeMember
  have routeLength := presentation.contractedEdgeRoute_length_ge_two
    degree edgeMember
  have endpoints := presentation.contractedEdgeRoute_endpoints_of_mem
    edgeMember
  have graphEdgeMember : endpoint.edge.toPeriodicEdge ∈
      problem.contractedGraph.edges := by
    exact List.mem_map.mpr ⟨endpoint.edge, edgeMember, rfl⟩
  have endpointMembers := (contractedGraph_isWellFormed problem).2
    endpoint.edge.toPeriodicEdge graphEdgeMember
  cases endpoint with
  | source edge =>
      simp only [ContractedEndpoint.edge_source] at edgeMember routeMember routeLength endpoints
      simp only [ContractedEndpoint.edge_source] at graphEdgeMember endpointMembers
      generalize routeEq : presentation.contractedEdgeRoute edge = route at routeMember routeLength endpoints
      rcases route with _ | ⟨first, route⟩
      · simp at routeLength
      rcases route with _ | ⟨second, rest⟩
      · simp at routeLength
      let indexed : IndexedGridSegment :=
        ⟨problem.contractedEdges.idxOf edge, 0, ⟨first, second⟩⟩
      have indexedMember :
          indexed ∈ presentation.contractedDrawing.indexedSegments := by
        apply PeriodicGridDrawing.mem_indexedSegments_iff.mpr
        refine ⟨first :: second :: rest, routeMember, ?_⟩
        simp [indexed, gridPolylineSegments]
      have startEq :
          first = presentation.contractedDrawing.vertexPosition
            problem.contractedGraph edge.toPeriodicEdge.source := by
        have original :
            first = presentation.drawing.vertexPosition
              problem.incidenceGraph edge.toPeriodicEdge.source := by
          simpa using Option.some.inj endpoints.1
        rw [presentation.contractedDrawing_vertexPosition endpointMembers.1]
        exact original
      exact ⟨{
        indexed := indexed
        indexedMember := indexedMember
        translate := (0, 0)
        reversed := false
        routeIndex_eq := rfl
        startsAt := by
          simpa [indexed, GridSegment.translate,
            ContractedEndpoint.vertex,
            PeriodicGridDrawing.periodTranslation, Cell.scale,
            Cell.add] using startEq
        direction_eq := by
          simp only [indexed, GridSegment.translate]
          rw [AxisDirection.between_add_left]
          change AxisDirection.between first second =
            AxisDirection.polylineFirstDirection
              (presentation.contractedEdgeRoute edge)
          rw [routeEq]
          rfl
      }⟩
  | target edge =>
      simp only [ContractedEndpoint.edge_target] at edgeMember routeMember routeLength endpoints
      simp only [ContractedEndpoint.edge_target] at graphEdgeMember endpointMembers
      let route := presentation.contractedEdgeRoute edge
      rcases AxisDirection.exists_eq_append_pair_of_length_ge_two
          routeLength with ⟨leading, before, last, routeEq⟩
      have finalSegmentMember :
          (GridSegment.mk before last) ∈ gridPolylineSegments route := by
        change (GridSegment.mk before last) ∈
          gridPolylineSegments (presentation.contractedEdgeRoute edge)
        rw [routeEq]
        rw [show leading ++ [before, last] =
          (leading ++ [before]) ++ [last] by simp]
        rw [gridPolylineSegments_append_singleton_of_ne_nil
          (leading ++ [before]) before last (by simp)]
        simp
      rcases List.mem_iff_get.mp finalSegmentMember with
        ⟨segmentIndex, segmentAt⟩
      let indexed : IndexedGridSegment :=
        ⟨problem.contractedEdges.idxOf edge, segmentIndex,
          ⟨before, last⟩⟩
      have segmentZipMember :
          (GridSegment.mk before last, segmentIndex.val) ∈
            (gridPolylineSegments route).zipIdx := by
        rw [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_some_iff]
        exact ⟨segmentIndex.isLt, segmentAt⟩
      have indexedMember :
          indexed ∈ presentation.contractedDrawing.indexedSegments := by
        apply PeriodicGridDrawing.mem_indexedSegments_iff.mpr
        exact ⟨route, routeMember, segmentZipMember⟩
      have finalAligned :
          (GridSegment.mk before last).IsAxisAligned := by
        have routeOrthogonal := presentation.contractedEdgeRoute_orthogonal_of_mem
          edgeMember
        rw [routeEq] at routeOrthogonal
        exact (List.isChain_append_cons_cons.mp routeOrthogonal).2.1
      have lastEq :
          last = Cell.add
            (presentation.drawing.vertexPosition
              problem.incidenceGraph edge.toPeriodicEdge.target)
            (presentation.drawing.periodTranslation
              edge.toPeriodicEdge.offset) := by
        apply Option.some.inj
        calc
          some last =
              (presentation.contractedEdgeRoute edge).getLast? := by
            rw [routeEq]
            simp
          _ = some (Cell.add
                (presentation.drawing.vertexPosition
                  problem.incidenceGraph edge.toPeriodicEdge.target)
                (presentation.drawing.periodTranslation
                  edge.toPeriodicEdge.offset)) := endpoints.2
      have targetPositionEq :
          presentation.contractedDrawing.vertexPosition
              problem.contractedGraph edge.toPeriodicEdge.target =
            presentation.drawing.vertexPosition
              problem.incidenceGraph edge.toPeriodicEdge.target :=
        presentation.contractedDrawing_vertexPosition endpointMembers.2
      exact ⟨{
        indexed := indexed
        indexedMember := indexedMember
        translate := (-edge.toPeriodicEdge.offset.1,
          -edge.toPeriodicEdge.offset.2)
        reversed := true
        routeIndex_eq := rfl
        startsAt := by
          simp only [indexed, if_true, GridSegment.reverse,
            GridSegment.translate]
          rw [lastEq]
          simp only [ContractedEndpoint.vertex]
          rw [targetPositionEq]
          rcases edge.toPeriodicEdge.offset with ⟨offsetX, offsetY⟩
          rcases presentation.drawing.vertexPosition problem.incidenceGraph
              edge.toPeriodicEdge.target with ⟨targetX, targetY⟩
          simp [PlanarPresentation.contractedDrawing,
            PeriodicGridDrawing.periodTranslation,
            PeriodicGridDrawing.gridSize, Cell.scale, Cell.add]
        direction_eq := by
          simp only [indexed, if_true, GridSegment.reverse,
            GridSegment.translate]
          rw [AxisDirection.between_add_left]
          rw [AxisDirection.between_reverse_eq_opposite
            (AxisDirection.between_isGenuine_of_axisAligned finalAligned)]
          change
            (AxisDirection.between before last).opposite =
              (AxisDirection.polylineLastDirection
                (presentation.contractedEdgeRoute edge)).opposite
          rw [routeEq]
          rw [AxisDirection.polylineLastDirection_append_pair_of_axisAligned
            leading finalAligned]
      }⟩

end PeriodicThreeDM
end LeanTrominoes
