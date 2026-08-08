import LeanTrominoes.PeriodicGridDrawingIndexedSegmentLookup
import LeanTrominoes.PeriodicGridDrawingRouteSimplicity

/-!
# Covering periodic drawing vertices by segment endpoints

For periodic drawings it is useful to separate the combinatorial fact that
every stored graph vertex is an endpoint of some lifted segment from the
geometric fact that routes avoid one another.  The former and orthogonality
turn global route separation into vertex/interior avoidance.
-/

namespace LeanTrominoes
namespace PeriodicGridDrawing

/-- Every stored graph-vertex position is an endpoint of some segment
occurrence in the infinite periodic lift. -/
def VertexPositionsCoveredBySegmentEndpoints
    (drawing : PeriodicGridDrawing) : Prop :=
  ∀ vertexPosition ∈ drawing.vertexPositions,
    ∃ indexed ∈ drawing.indexedSegments,
      ∃ translate : Cell,
        vertexPosition =
            (indexed.segment.translate
              (drawing.periodTranslation translate)).start ∨
          vertexPosition =
            (indexed.segment.translate
              (drawing.periodTranslation translate)).finish

/-- The relative interior of each lifted segment avoids both endpoints of
every distinct lifted segment occurrence.  Unlike `RoutesAvoidInteriors`,
this predicate still records endpoint separation when the second segment
is diagonal. -/
def SegmentEndpointsAvoidInteriors
    (drawing : PeriodicGridDrawing) : Prop :=
  ∀ first ∈ drawing.indexedSegments,
    ∀ second ∈ drawing.indexedSegments,
      ∀ firstTranslate secondTranslate point,
        SegmentOccurrenceKey first firstTranslate ≠
            SegmentOccurrenceKey second secondTranslate →
          (first.segment.translate
              (drawing.periodTranslation firstTranslate)).InteriorContains
            point →
          point ≠
              (second.segment.translate
                (drawing.periodTranslation secondTranslate)).start ∧
            point ≠
              (second.segment.translate
                (drawing.periodTranslation secondTranslate)).finish

/-- Every listed protovertex is an endpoint of at least one listed
protoedge. -/
def EveryVertexIncident {Vertex : Type*}
    (graph : PeriodicGraph Vertex) : Prop :=
  ∀ vertex ∈ graph.vertices,
    ∃ taggedEdge ∈ graph.edges.zipIdx,
      taggedEdge.1.source = vertex ∨ taggedEdge.1.target = vertex

/-- Every protoedge route contains at least one genuine segment. -/
def EdgeRoutesHaveSegments {Vertex : Type*}
    (graph : PeriodicGraph Vertex)
    (drawing : PeriodicGridDrawing) : Prop :=
  ∀ taggedEdge ∈ graph.edges.zipIdx,
    2 ≤ (drawing.edgeRoute taggedEdge.2).length

/-- No listed protoedge has the same prototype vertex at both ends. -/
def EdgesAreLoopless {Vertex : Type*}
    (graph : PeriodicGraph Vertex) : Prop :=
  ∀ edge ∈ graph.edges, edge.source ≠ edge.target

/-- Membership of every listed vertex in the flat edge-end list is exactly
the combinatorial information needed to choose an incident tagged edge. -/
theorem everyVertexIncident_of_mem_incidences
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (covered :
      ∀ vertex ∈ graph.vertices, vertex ∈ graph.incidences) :
    EveryVertexIncident graph := by
  intro vertex vertexMember
  have incidenceMember := covered vertex vertexMember
  unfold PeriodicGraph.incidences at incidenceMember
  rcases List.mem_flatMap.mp incidenceMember with
    ⟨edge, edgeMember, endpointMember⟩
  rcases List.mem_iff_get.mp edgeMember with
    ⟨edgeIndex, edgeAt⟩
  have taggedMember :
      (edge, edgeIndex.val) ∈ graph.edges.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?,
      List.getElem?_eq_some_iff]
    exact ⟨edgeIndex.isLt, edgeAt⟩
  refine ⟨(edge, edgeIndex.val), taggedMember, ?_⟩
  simpa [PeriodicEdge.incidences, eq_comm] using endpointMember

/-- Compatibility makes the stored position lookup an actual member of the
drawing's position list. -/
theorem IsCompatible.vertexPosition_mem
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing}
    (compatible : drawing.IsCompatible graph)
    {vertex : Vertex}
    (vertexMember : vertex ∈ graph.vertices) :
    drawing.vertexPosition graph vertex ∈ drawing.vertexPositions := by
  have vertexIndexLt :
      graph.vertices.idxOf vertex < graph.vertices.length :=
    List.idxOf_lt_length_iff.mpr vertexMember
  have positionIndexLt :
      graph.vertices.idxOf vertex < drawing.vertexPositions.length := by
    rwa [compatible.2.1]
  unfold vertexPosition
  rw [List.getD_eq_getElem _ _ positionIndexLt]
  exact List.getElem_mem positionIndexLt

/-- Distinct listed protovertices have distinct compatible drawing
positions. -/
theorem IsCompatible.vertexPosition_injective_on
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing}
    (compatible : drawing.IsCompatible graph)
    {first second : Vertex}
    (firstMember : first ∈ graph.vertices)
    (secondMember : second ∈ graph.vertices)
    (equal :
      drawing.vertexPosition graph first =
        drawing.vertexPosition graph second) :
    first = second := by
  have firstIndexLt :
      graph.vertices.idxOf first < graph.vertices.length :=
    List.idxOf_lt_length_iff.mpr firstMember
  have secondIndexLt :
      graph.vertices.idxOf second < graph.vertices.length :=
    List.idxOf_lt_length_iff.mpr secondMember
  have firstPositionLt :
      graph.vertices.idxOf first < drawing.vertexPositions.length := by
    rwa [compatible.2.1]
  have secondPositionLt :
      graph.vertices.idxOf second < drawing.vertexPositions.length := by
    rwa [compatible.2.1]
  unfold vertexPosition at equal
  rw [List.getD_eq_getElem _ _ firstPositionLt,
    List.getD_eq_getElem _ _ secondPositionLt] at equal
  have indicesEqual :
      graph.vertices.idxOf first =
        graph.vertices.idxOf second :=
    (compatible.2.2.2.1.getElem_inj_iff).mp equal
  calc
    first =
        graph.vertices[
          graph.vertices.idxOf first]'firstIndexLt :=
      (List.idxOf_get firstIndexLt).symm
    _ =
        graph.vertices[
          graph.vertices.idxOf second]'secondIndexLt := by
      congr
    _ = second :=
      List.idxOf_get secondIndexLt

/-- A route selected by a tagged graph edge occurs at that same index in a
compatible drawing's flat route list. -/
private theorem edgeRoute_mem_zipIdx
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing}
    (compatible : drawing.IsCompatible graph)
    {taggedEdge : PeriodicEdge Vertex × Nat}
    (edgeMember : taggedEdge ∈ graph.edges.zipIdx) :
    (drawing.edgeRoute taggedEdge.2, taggedEdge.2) ∈
      drawing.edgeRoutes.zipIdx := by
  have edgeIndexLt :
      taggedEdge.2 < graph.edges.length :=
    List.snd_lt_of_mem_zipIdx edgeMember
  have routeIndexLt :
      taggedEdge.2 < drawing.edgeRoutes.length := by
    rwa [compatible.2.2.1]
  rw [List.mem_zipIdx_iff_getElem?,
    List.getElem?_eq_some_iff]
  refine ⟨routeIndexLt, ?_⟩
  unfold edgeRoute
  rw [List.getD_eq_getElem _ _ routeIndexLt]

/-- Incidence and nondegeneracy convert exact compatible route endpoints
into endpoint coverage of every stored graph vertex. -/
theorem vertexPositionsCoveredBySegmentEndpoints_of_compatible
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (drawing : PeriodicGridDrawing)
    (compatible : drawing.IsCompatible graph)
    (incident : EveryVertexIncident graph)
    (routesHaveSegments : EdgeRoutesHaveSegments graph drawing) :
    drawing.VertexPositionsCoveredBySegmentEndpoints := by
  intro vertexPosition vertexPositionMember
  rcases List.mem_iff_get.mp vertexPositionMember with
    ⟨positionIndex, positionAt⟩
  have graphIndexLt :
      positionIndex.val < graph.vertices.length := by
    rw [← compatible.2.1]
    exact positionIndex.isLt
  let graphIndex : Fin graph.vertices.length :=
    ⟨positionIndex.val, graphIndexLt⟩
  let vertex := graph.vertices.get graphIndex
  have vertexMember : vertex ∈ graph.vertices :=
    List.get_mem graph.vertices graphIndex
  have vertexIndexEq :
      graph.vertices.idxOf vertex = graphIndex.val := by
    exact compatible.1.1.idxOf_getElem graphIndex.val graphIndexLt
  have vertexPositionEq :
      drawing.vertexPosition graph vertex = vertexPosition := by
    unfold PeriodicGridDrawing.vertexPosition
    rw [vertexIndexEq,
      List.getD_eq_getElem _ _ positionIndex.isLt]
    exact positionAt
  rcases incident vertex vertexMember with
    ⟨taggedEdge, taggedEdgeMember, source | target⟩
  · have routeMember :=
      edgeRoute_mem_zipIdx compatible taggedEdgeMember
    have endpoints :=
      compatible.2.2.2.2.2 taggedEdge taggedEdgeMember
    have sourceMember :
        drawing.vertexPosition graph taggedEdge.1.source ∈
          drawing.edgeRoute taggedEdge.2 :=
      List.mem_of_mem_head? (by simp [endpoints.1])
    rcases
        PeriodicOrthocrossing.exists_segment_endpoint_of_mem
          (routesHaveSegments taggedEdge taggedEdgeMember)
          sourceMember with
      ⟨segment, segmentMember, endpoint⟩
    rcases List.mem_iff_get.mp segmentMember with
      ⟨segmentIndex, segmentAt⟩
    let indexed : IndexedGridSegment :=
      ⟨taggedEdge.2, segmentIndex, segment⟩
    have indexedMember : indexed ∈ drawing.indexedSegments := by
      have member :=
        indexedSegment_mem_of_route_mem routeMember segmentIndex
      rw [segmentAt] at member
      simpa only [indexed] using member
    refine ⟨indexed, indexedMember, (0, 0), ?_⟩
    have pointEq :
        vertexPosition =
          drawing.vertexPosition graph taggedEdge.1.source := by
      rw [source]
      exact vertexPositionEq.symm
    rcases endpoint with endpoint | endpoint
    · left
      simpa [indexed, GridSegment.translate,
        PeriodicGridDrawing.periodTranslation,
        Cell.scale, Cell.add] using pointEq.trans endpoint
    · right
      simpa [indexed, GridSegment.translate,
        PeriodicGridDrawing.periodTranslation,
        Cell.scale, Cell.add] using pointEq.trans endpoint
  · have routeMember :=
      edgeRoute_mem_zipIdx compatible taggedEdgeMember
    have endpoints :=
      compatible.2.2.2.2.2 taggedEdge taggedEdgeMember
    have targetMember :
        Cell.add
            (drawing.vertexPosition graph taggedEdge.1.target)
            (drawing.periodTranslation taggedEdge.1.offset) ∈
          drawing.edgeRoute taggedEdge.2 :=
      mem_of_getLast?_eq_some endpoints.2
    rcases
        PeriodicOrthocrossing.exists_segment_endpoint_of_mem
          (routesHaveSegments taggedEdge taggedEdgeMember)
          targetMember with
      ⟨segment, segmentMember, endpoint⟩
    rcases List.mem_iff_get.mp segmentMember with
      ⟨segmentIndex, segmentAt⟩
    let indexed : IndexedGridSegment :=
      ⟨taggedEdge.2, segmentIndex, segment⟩
    have indexedMember : indexed ∈ drawing.indexedSegments := by
      have member :=
        indexedSegment_mem_of_route_mem routeMember segmentIndex
      rw [segmentAt] at member
      simpa only [indexed] using member
    let reverseOffset : Cell :=
      (-taggedEdge.1.offset.1, -taggedEdge.1.offset.2)
    refine ⟨indexed, indexedMember, reverseOffset, ?_⟩
    have pointEq :
        vertexPosition =
          drawing.vertexPosition graph taggedEdge.1.target := by
      rw [target]
      exact vertexPositionEq.symm
    rcases taggedEdge.1.offset with ⟨offsetX, offsetY⟩
    rcases segment with ⟨⟨startX, startY⟩, ⟨finishX, finishY⟩⟩
    simp only [PeriodicGridDrawing.periodTranslation,
      Cell.scale, Cell.add, Prod.mk.injEq] at endpoint
    rcases endpoint with endpoint | endpoint
    · left
      rw [pointEq]
      apply Prod.ext
      · dsimp [reverseOffset, indexed, GridSegment.translate,
          PeriodicGridDrawing.periodTranslation, Cell.scale, Cell.add]
        rw [← endpoint.1]
        ring
      · dsimp [reverseOffset, indexed, GridSegment.translate,
          PeriodicGridDrawing.periodTranslation, Cell.scale, Cell.add]
        rw [← endpoint.2]
        ring
    · right
      rw [pointEq]
      apply Prod.ext
      · dsimp [reverseOffset, indexed, GridSegment.translate,
          PeriodicGridDrawing.periodTranslation, Cell.scale, Cell.add]
        rw [← endpoint.1]
        ring
      · dsimp [reverseOffset, indexed, GridSegment.translate,
          PeriodicGridDrawing.periodTranslation, Cell.scale, Cell.add]
        rw [← endpoint.2]
        ring

/-- Translating a covered segment occurrence and its endpoint by the same
additional period preserves the endpoint equation. -/
private theorem add_periodTranslation_eq_translated_endpoint
    (drawing : PeriodicGridDrawing)
    (segment : GridSegment)
    (coverTranslate vertexTranslate vertexPosition : Cell)
    (endpoint :
      vertexPosition =
          (segment.translate
            (drawing.periodTranslation coverTranslate)).start ∨
        vertexPosition =
          (segment.translate
            (drawing.periodTranslation coverTranslate)).finish) :
    Cell.add vertexPosition
        (drawing.periodTranslation vertexTranslate) =
          (segment.translate
            (drawing.periodTranslation
              (Cell.add coverTranslate vertexTranslate))).start ∨
      Cell.add vertexPosition
        (drawing.periodTranslation vertexTranslate) =
          (segment.translate
            (drawing.periodTranslation
              (Cell.add coverTranslate vertexTranslate))).finish := by
  rcases segment with ⟨⟨startX, startY⟩, ⟨finishX, finishY⟩⟩
  rcases coverTranslate with ⟨coverX, coverY⟩
  rcases vertexTranslate with ⟨vertexX, vertexY⟩
  rcases vertexPosition with ⟨positionX, positionY⟩
  simp only [GridSegment.translate, PeriodicGridDrawing.periodTranslation,
    Cell.scale, Cell.add, Prod.mk.injEq] at endpoint ⊢
  rcases endpoint with endpoint | endpoint
  · left
    constructor
    · rw [endpoint.1]
      ring
    · rw [endpoint.2]
      ring
  · right
    constructor
    · rw [endpoint.1]
      ring
    · rw [endpoint.2]
      ring

/-- Endpoint coverage converts ordered route separation into the global
vertex/interior avoidance predicate. -/
theorem verticesAvoidRouteInteriors_of_endpointCoverage
    (drawing : PeriodicGridDrawing)
    (covered : drawing.VertexPositionsCoveredBySegmentEndpoints)
    (orthogonal : drawing.IsOrthogonal)
    (routesAvoidInteriors : drawing.RoutesAvoidInteriors) :
    drawing.VerticesAvoidRouteInteriors := by
  intro vertexPosition vertexMember indexed indexedMember
    vertexTranslate routeTranslate interior
  rcases covered vertexPosition vertexMember with
    ⟨covering, coveringMember, coverTranslate, endpoint⟩
  let liftedCoverTranslate : Cell :=
    Cell.add coverTranslate vertexTranslate
  have liftedEndpoint :
      Cell.add vertexPosition
          (drawing.periodTranslation vertexTranslate) =
            (covering.segment.translate
              (drawing.periodTranslation liftedCoverTranslate)).start ∨
        Cell.add vertexPosition
          (drawing.periodTranslation vertexTranslate) =
            (covering.segment.translate
              (drawing.periodTranslation liftedCoverTranslate)).finish := by
    exact
      add_periodTranslation_eq_translated_endpoint
        drawing covering.segment coverTranslate vertexTranslate
        vertexPosition endpoint
  by_cases different :
      SegmentOccurrenceKey indexed routeTranslate ≠
        SegmentOccurrenceKey covering liftedCoverTranslate
  · apply
      routesAvoidInteriors indexed indexedMember
        covering coveringMember routeTranslate liftedCoverTranslate
        (Cell.add vertexPosition
          (drawing.periodTranslation vertexTranslate))
        different interior
    have translatedAligned :
        (covering.segment.translate
          (drawing.periodTranslation liftedCoverTranslate)).IsAxisAligned :=
      (GridSegment.isAxisAligned_translate _ _).mpr
        (orthogonal covering coveringMember)
    rcases liftedEndpoint with endpointStart | endpointFinish
    · rw [endpointStart]
      exact
        GridSegment.contains_start_of_axisAligned translatedAligned
    · rw [endpointFinish]
      exact
        GridSegment.contains_finish_of_axisAligned translatedAligned
  · have keyEq :
        SegmentOccurrenceKey indexed routeTranslate =
          SegmentOccurrenceKey covering liftedCoverTranslate :=
      not_ne_iff.mp different
    have routeIndexEq :
        indexed.routeIndex = covering.routeIndex :=
      congrArg (fun key => key.1) keyEq
    have segmentIndexEq :
        indexed.segmentIndex = covering.segmentIndex :=
      congrArg (fun key => key.2.1) keyEq
    have translateEq :
        routeTranslate = liftedCoverTranslate :=
      congrArg (fun key => key.2.2) keyEq
    have indexedEq : indexed = covering :=
      eq_of_mem_indexedSegments_of_indices_eq
        indexedMember coveringMember routeIndexEq segmentIndexEq
    subst covering
    rw [← translateEq] at liftedEndpoint
    rcases liftedEndpoint with endpointStart | endpointFinish
    · rw [endpointStart] at interior
      exact
        GridSegment.not_interiorContains_start
          (indexed.segment.translate
            (drawing.periodTranslation routeTranslate)) interior
    · rw [endpointFinish] at interior
      exact
        GridSegment.not_interiorContains_finish
          (indexed.segment.translate
            (drawing.periodTranslation routeTranslate)) interior

/-- Endpoint coverage and endpoint-aware segment separation imply global
vertex/interior avoidance without assuming that every covering segment is
axis-aligned. -/
theorem
    verticesAvoidRouteInteriors_of_endpointCoverage_of_segmentEndpointsAvoidInteriors
    (drawing : PeriodicGridDrawing)
    (covered : drawing.VertexPositionsCoveredBySegmentEndpoints)
    (endpointsAvoid : drawing.SegmentEndpointsAvoidInteriors) :
    drawing.VerticesAvoidRouteInteriors := by
  intro vertexPosition vertexMember indexed indexedMember
    vertexTranslate routeTranslate interior
  rcases covered vertexPosition vertexMember with
    ⟨covering, coveringMember, coverTranslate, endpoint⟩
  let liftedCoverTranslate : Cell :=
    Cell.add coverTranslate vertexTranslate
  have liftedEndpoint :
      Cell.add vertexPosition
          (drawing.periodTranslation vertexTranslate) =
            (covering.segment.translate
              (drawing.periodTranslation liftedCoverTranslate)).start ∨
        Cell.add vertexPosition
          (drawing.periodTranslation vertexTranslate) =
            (covering.segment.translate
              (drawing.periodTranslation liftedCoverTranslate)).finish := by
    exact
      add_periodTranslation_eq_translated_endpoint
        drawing covering.segment coverTranslate vertexTranslate
        vertexPosition endpoint
  by_cases different :
      SegmentOccurrenceKey indexed routeTranslate ≠
        SegmentOccurrenceKey covering liftedCoverTranslate
  · have avoids :=
      endpointsAvoid indexed indexedMember
        covering coveringMember routeTranslate liftedCoverTranslate
        (Cell.add vertexPosition
          (drawing.periodTranslation vertexTranslate))
        different interior
    rcases liftedEndpoint with endpointStart | endpointFinish
    · exact avoids.1 endpointStart
    · exact avoids.2 endpointFinish
  · have keyEq :
        SegmentOccurrenceKey indexed routeTranslate =
          SegmentOccurrenceKey covering liftedCoverTranslate :=
      not_ne_iff.mp different
    have routeIndexEq :
        indexed.routeIndex = covering.routeIndex :=
      congrArg (fun key => key.1) keyEq
    have segmentIndexEq :
        indexed.segmentIndex = covering.segmentIndex :=
      congrArg (fun key => key.2.1) keyEq
    have translateEq :
        routeTranslate = liftedCoverTranslate :=
      congrArg (fun key => key.2.2) keyEq
    have indexedEq : indexed = covering :=
      eq_of_mem_indexedSegments_of_indices_eq
        indexedMember coveringMember routeIndexEq segmentIndexEq
    subst covering
    rw [← translateEq] at liftedEndpoint
    rcases liftedEndpoint with endpointStart | endpointFinish
    · rw [endpointStart] at interior
      exact
        GridSegment.not_interiorContains_start
          (indexed.segment.translate
            (drawing.periodTranslation routeTranslate)) interior
    · rw [endpointFinish] at interior
      exact
        GridSegment.not_interiorContains_finish
          (indexed.segment.translate
            (drawing.periodTranslation routeTranslate)) interior

end PeriodicGridDrawing
end LeanTrominoes
