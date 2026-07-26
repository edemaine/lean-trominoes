import LeanTrominoes.PeriodicOrthocrossingPorts
import Mathlib.Data.List.Chain

/-!
# Orthogonality of the periodic track construction

Locality restricts every edge offset to the origin or one of four cardinal
neighbors.  Together with the private-column and private-track bounds, this
makes every consecutive pair in each generated route a nondegenerate
horizontal or vertical segment.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- The five possible offsets of a local protoedge. -/
theorem offset_eq_of_span_le_one {Vertex : Type*}
    (edge : PeriodicEdge Vertex) (hLocal : edge.span ≤ 1) :
    edge.offset = (0, 0) ∨ edge.offset = (1, 0) ∨
      edge.offset = (-1, 0) ∨ edge.offset = (0, 1) ∨
      edge.offset = (0, -1) := by
  rcases edge with ⟨source, target, ⟨horizontal, vertical⟩⟩
  change horizontal.natAbs + vertical.natAbs ≤ 1 at hLocal
  have horizontalAbs : horizontal.natAbs ≤ 1 := by
    omega
  have verticalAbs : vertical.natAbs ≤ 1 := by
    omega
  have horizontalCast : (horizontal.natAbs : Int) ≤ 1 := by
    exact_mod_cast horizontalAbs
  have verticalCast : (vertical.natAbs : Int) ≤ 1 := by
    exact_mod_cast verticalAbs
  rw [Int.natCast_natAbs] at horizontalCast verticalCast
  have horizontalBounds := abs_le.mp horizontalCast
  have verticalBounds := abs_le.mp verticalCast
  have horizontalCases :
      horizontal = -1 ∨ horizontal = 0 ∨ horizontal = 1 := by
    omega
  have verticalCases :
      vertical = -1 ∨ vertical = 0 ∨ vertical = 1 := by
    omega
  rcases horizontalCases with rfl | rfl | rfl <;>
    rcases verticalCases with rfl | rfl | rfl <;>
    simp at hLocal ⊢

theorem portX_bounds {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    {port : GraphPort Vertex} (portMem : port ∈ allPorts graph) :
    0 < portX graph port ∧
      portX graph port < drawingGridSize graph := by
  have vertexMem := port_vertex_mem wellFormed portMem
  have vertexIndexLt :
      graph.vertices.idxOf port.vertex < graph.vertices.length :=
    List.idxOf_lt_length_iff.mpr vertexMem
  have rankLt := portRank_lt_three degree portMem
  unfold portX vertexX drawingGridSize
  norm_num
  omega

theorem edgeTrack_bounds {Vertex : Type*}
    (graph : PeriodicGraph Vertex)
    {taggedEdge : PeriodicEdge Vertex × Nat}
    (edgeMem : taggedEdge ∈ graph.edges.zipIdx) :
    3 < edgeTrack taggedEdge.2 ∧
      edgeTrack taggedEdge.2 + 1 < drawingGridSize graph := by
  have edgeIndexLt : taggedEdge.2 < graph.edges.length := by
    simpa using List.snd_lt_of_mem_zipIdx edgeMem
  unfold edgeTrack drawingGridSize
  omega

theorem edgeGateX_bounds {Vertex : Type*}
    (graph : PeriodicGraph Vertex)
    {taggedEdge : PeriodicEdge Vertex × Nat}
    (edgeMem : taggedEdge ∈ graph.edges.zipIdx) :
    0 < edgeGateX graph taggedEdge.2 ∧
      edgeGateX graph taggedEdge.2 < drawingGridSize graph := by
  have edgeIndexLt : taggedEdge.2 < graph.edges.length := by
    simpa using List.snd_lt_of_mem_zipIdx edgeMem
  unfold edgeGateX drawingGridSize
  norm_num
  omega

theorem portX_lt_edgeGateX {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    {port : GraphPort Vertex} (portMem : port ∈ allPorts graph)
    (edgeIndex : Nat) :
    portX graph port < edgeGateX graph edgeIndex := by
  have vertexMem := port_vertex_mem wellFormed portMem
  have vertexIndexLt :
      graph.vertices.idxOf port.vertex < graph.vertices.length :=
    List.idxOf_lt_length_iff.mpr vertexMem
  have rankLt := portRank_lt_three degree portMem
  unfold portX vertexX edgeGateX
  omega

/-- Pointwise formulation of an orthogonal polyline. -/
def OrthogonalPolyline (points : List Cell) : Prop :=
  points.IsChain fun first second =>
    (GridSegment.mk first second).IsAxisAligned

theorem orthogonalPolyline_iff_segments (points : List Cell) :
    OrthogonalPolyline points ↔
      ∀ segment ∈ gridPolylineSegments points, segment.IsAxisAligned := by
  induction points using List.twoStepInduction with
  | nil | singleton =>
      simp [OrthogonalPolyline, gridPolylineSegments]
  | cons_cons first second rest _ tailInduction =>
      constructor
      · intro chain segment segmentMem
        have parts :=
          (List.isChain_cons_cons.mp chain :
            (GridSegment.mk first second).IsAxisAligned ∧
              OrthogonalPolyline (second :: rest))
        simp only [gridPolylineSegments, List.mem_cons] at segmentMem
        rcases segmentMem with rfl | segmentMem
        · exact parts.1
        · exact (tailInduction second).mp parts.2 segment segmentMem
      · intro segments
        apply List.isChain_cons_cons.mpr
        constructor
        · exact segments (GridSegment.mk first second) (by simp
            [gridPolylineSegments])
        · apply (tailInduction second).mpr
          intro segment segmentMem
          exact segments segment (by simp [gridPolylineSegments, segmentMem])

end PeriodicOrthocrossing

/-- The indexed-segment definition of drawing orthogonality is equivalent
to checking every route as an orthogonal polyline. -/
theorem PeriodicGridDrawing.isOrthogonal_iff_routes
    (drawing : PeriodicGridDrawing) :
    drawing.IsOrthogonal ↔
      ∀ route ∈ drawing.edgeRoutes,
        PeriodicOrthocrossing.OrthogonalPolyline route := by
  constructor
  · intro orthogonal route routeMem
    apply
      (PeriodicOrthocrossing.orthogonalPolyline_iff_segments
        route).2
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
      (PeriodicOrthocrossing.orthogonalPolyline_iff_segments
        taggedRoute.1).1
        (routes taggedRoute.1
          (List.fst_mem_of_mem_zipIdx taggedRouteMem))
        taggedSegment.1
        (List.fst_mem_of_mem_zipIdx taggedSegmentMem)

namespace PeriodicOrthocrossing

theorem isChain_joinPolylines {relation : Cell → Cell → Prop}
    {first second : List Cell}
    (firstChain : first.IsChain relation)
    (secondChain : second.IsChain relation)
    (boundary : first.getLast? = second.head?) :
    (joinPolylines first second).IsChain relation := by
  cases second with
  | nil =>
      simpa [joinPolylines] using firstChain
  | cons secondHead secondTail =>
      cases secondTail with
      | nil =>
          simpa [joinPolylines] using firstChain
      | cons next rest =>
          apply firstChain.append secondChain.tail
          intro firstLast firstLastMem secondFirst secondFirstMem
          have firstLastEq : firstLast = secondHead := by
            simpa [boundary] using firstLastMem.symm
          have secondFirstEq : secondFirst = next := by
            simpa using secondFirstMem.symm
          subst firstLast
          subst secondFirst
          exact (List.isChain_cons_cons.mp secondChain).1

@[simp]
theorem fanout_head? (centerX portColumn : Int) :
    (fanout centerX portColumn).head? = some (centerX, 2) := by
  by_cases same : centerX = portColumn <;> simp [fanout, same]

@[simp]
theorem fanout_getLast? (centerX portColumn : Int) :
    (fanout centerX portColumn).getLast? = some (portColumn, 3) := by
  by_cases same : centerX = portColumn <;> simp [fanout, same]

theorem fanout_orthogonal (centerX portColumn : Int) :
    OrthogonalPolyline (fanout centerX portColumn) := by
  by_cases same : centerX = portColumn
  · subst portColumn
    simp [OrthogonalPolyline, fanout, GridSegment.IsAxisAligned,
      GridSegment.IsHorizontal, GridSegment.IsVertical]
  · simp [OrthogonalPolyline, fanout, same, GridSegment.IsAxisAligned,
      GridSegment.IsHorizontal, GridSegment.IsVertical]

theorem translated_reverse_fanout_orthogonal
    (centerX portColumn : Int) (translate : Cell) :
    OrthogonalPolyline
      (translatePolyline translate (fanout centerX portColumn).reverse) := by
  by_cases same : centerX = portColumn
  · subst portColumn
    simp [OrthogonalPolyline, translatePolyline, fanout, Cell.add,
      GridSegment.IsAxisAligned, GridSegment.IsHorizontal,
      GridSegment.IsVertical]
  · simp [OrthogonalPolyline, translatePolyline, fanout, same, Cell.add,
      Ne.symm same, GridSegment.IsAxisAligned, GridSegment.IsHorizontal,
      GridSegment.IsVertical]

@[simp]
theorem edgeCore_head? {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (edge : PeriodicEdge Vertex) (edgeIndex : Nat) :
    (edgeCore graph edge edgeIndex).head? =
      some (portX graph (sourcePort edge edgeIndex), 3) := by
  unfold edgeCore
  split <;> simp_all
  all_goals split <;> simp_all

@[simp]
theorem edgeCore_getLast? {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (edge : PeriodicEdge Vertex) (edgeIndex : Nat) :
    (edgeCore graph edge edgeIndex).getLast? =
      some (Cell.add
        (portX graph (targetPort edge edgeIndex), 3)
        (Cell.scale (drawingGridSize graph : Int) edge.offset)) := by
  unfold edgeCore
  split <;> simp_all
  all_goals split <;> simp_all

theorem edgeCore_length_ge_two {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (edge : PeriodicEdge Vertex) (edgeIndex : Nat) :
    2 ≤ (edgeCore graph edge edgeIndex).length := by
  unfold edgeCore
  split <;> simp_all
  all_goals split <;> simp_all

/-- The private-track core of every local edge is orthogonal. -/
theorem edgeCore_orthogonal {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    {taggedEdge : PeriodicEdge Vertex × Nat}
    (edgeMem : taggedEdge ∈ graph.edges.zipIdx)
    (edgeLocal : taggedEdge.1.span ≤ 1) :
    OrthogonalPolyline
      (edgeCore graph taggedEdge.1 taggedEdge.2) := by
  let source := sourcePort taggedEdge.1 taggedEdge.2
  let target := targetPort taggedEdge.1 taggedEdge.2
  have sourceMem : source ∈ allPorts graph :=
    sourcePort_mem_allPorts graph edgeMem
  have targetMem : target ∈ allPorts graph :=
    targetPort_mem_allPorts graph edgeMem
  have sourceBounds := portX_bounds wellFormed degree sourceMem
  have targetBounds := portX_bounds wellFormed degree targetMem
  have sourceBeforeGate :=
    portX_lt_edgeGateX wellFormed degree sourceMem taggedEdge.2
  have targetBeforeGate :=
    portX_lt_edgeGateX wellFormed degree targetMem taggedEdge.2
  have tracks := edgeTrack_bounds graph edgeMem
  have gateBounds := edgeGateX_bounds graph edgeMem
  have portsDifferent :=
    sourcePortX_ne_targetPortX wellFormed degree edgeMem
  have sizePositive := drawingGridSize_pos graph
  dsimp [source, target] at sourceMem targetMem sourceBounds targetBounds sourceBeforeGate targetBeforeGate
  rcases offset_eq_of_span_le_one taggedEdge.1 edgeLocal with
      offset | offset | offset | offset | offset
  · simp [edgeCore, offset, OrthogonalPolyline,
      GridSegment.IsAxisAligned, GridSegment.IsHorizontal,
      GridSegment.IsVertical, Cell.add, Cell.scale] <;> omega
  · by_cases order :
        portX graph (targetPort taggedEdge.1 taggedEdge.2) <
          portX graph (sourcePort taggedEdge.1 taggedEdge.2)
    · simp [edgeCore, offset, order, OrthogonalPolyline,
        GridSegment.IsAxisAligned, GridSegment.IsHorizontal,
        GridSegment.IsVertical, Cell.add, Cell.scale] <;> omega
    · simp [edgeCore, offset, order, OrthogonalPolyline,
        GridSegment.IsAxisAligned, GridSegment.IsHorizontal,
        GridSegment.IsVertical, Cell.add, Cell.scale] <;> omega
  · by_cases order :
        portX graph (sourcePort taggedEdge.1 taggedEdge.2) <
          portX graph (targetPort taggedEdge.1 taggedEdge.2)
    · simp [edgeCore, offset, order, OrthogonalPolyline,
        GridSegment.IsAxisAligned, GridSegment.IsHorizontal,
        GridSegment.IsVertical, Cell.add, Cell.scale] <;> omega
    · simp [edgeCore, offset, order, OrthogonalPolyline,
        GridSegment.IsAxisAligned, GridSegment.IsHorizontal,
        GridSegment.IsVertical, Cell.add, Cell.scale] <;> omega
  · simp [edgeCore, offset, OrthogonalPolyline,
      GridSegment.IsAxisAligned, GridSegment.IsHorizontal,
      GridSegment.IsVertical, Cell.add, Cell.scale] <;> omega
  · simp [edgeCore, offset, OrthogonalPolyline,
      GridSegment.IsAxisAligned, GridSegment.IsHorizontal,
      GridSegment.IsVertical, Cell.add, Cell.scale] <;> omega

/-- Each complete constructed edge route, including its source and target
fanouts, is orthogonal. -/
theorem constructedEdgeRoute_orthogonal {Vertex : Type*}
    [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    {taggedEdge : PeriodicEdge Vertex × Nat}
    (edgeMem : taggedEdge ∈ graph.edges.zipIdx)
    (edgeLocal : taggedEdge.1.span ≤ 1) :
    OrthogonalPolyline
      (constructedEdgeRoute graph taggedEdge.1 taggedEdge.2) := by
  let sourceCenter :=
    vertexX (graph.vertices.idxOf taggedEdge.1.source)
  let targetCenter :=
    vertexX (graph.vertices.idxOf taggedEdge.1.target)
  let sourceColumn :=
    portX graph (sourcePort taggedEdge.1 taggedEdge.2)
  let targetColumn :=
    portX graph (targetPort taggedEdge.1 taggedEdge.2)
  let targetTranslate :=
    Cell.scale (drawingGridSize graph : Int) taggedEdge.1.offset
  let sourceFanout := fanout sourceCenter sourceColumn
  let core := edgeCore graph taggedEdge.1 taggedEdge.2
  let targetFanout :=
    translatePolyline targetTranslate
      (fanout targetCenter targetColumn).reverse
  have sourceOrthogonal : OrthogonalPolyline sourceFanout := by
    exact fanout_orthogonal sourceCenter sourceColumn
  have coreOrthogonal : OrthogonalPolyline core := by
    exact edgeCore_orthogonal wellFormed degree edgeMem edgeLocal
  have targetOrthogonal : OrthogonalPolyline targetFanout := by
    exact translated_reverse_fanout_orthogonal
      targetCenter targetColumn targetTranslate
  have sourceBoundary :
      sourceFanout.getLast? = core.head? := by
    simp [sourceFanout, core, sourceColumn]
  have targetBoundary :
      core.getLast? = targetFanout.head? := by
    dsimp [core, targetFanout, targetTranslate, targetCenter, targetColumn]
    rw [edgeCore_getLast?]
    by_cases same :
        vertexX (graph.vertices.idxOf taggedEdge.1.target) =
          portX graph (targetPort taggedEdge.1 taggedEdge.2)
    · simp [translatePolyline, fanout, same, Cell.add, add_comm]
    · simp [translatePolyline, fanout, same, Cell.add, add_comm]
  have coreLong : 2 ≤ core.length := by
    exact edgeCore_length_ge_two graph taggedEdge.1 taggedEdge.2
  change OrthogonalPolyline
    (joinPolylines (joinPolylines sourceFanout core) targetFanout)
  apply isChain_joinPolylines
  · exact isChain_joinPolylines sourceOrthogonal coreOrthogonal sourceBoundary
  · exact targetOrthogonal
  · rw [joinPolylines_getLast?_of_second coreLong]
    exact targetBoundary

/-- The entire finite presentation produced from a local degree-three graph
is orthogonal. -/
theorem drawing_isOrthogonal {Vertex : Type*}
    [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (isLocal : graph.IsLocal)
    (degree : graph.DegreeAtMost 3) :
    (drawing graph).IsOrthogonal := by
  intro indexed indexedMem
  unfold PeriodicGridDrawing.indexedSegments at indexedMem
  rcases List.mem_flatMap.mp indexedMem with
    ⟨taggedRoute, taggedRouteMem, indexedMem⟩
  rcases List.mem_map.mp indexedMem with
    ⟨taggedSegment, taggedSegmentMem, rfl⟩
  have routeMem :
      taggedRoute.1 ∈ (drawing graph).edgeRoutes :=
    List.fst_mem_of_mem_zipIdx taggedRouteMem
  change taggedRoute.1 ∈ constructedEdgeRoutes graph at routeMem
  rw [constructedEdgeRoutes] at routeMem
  rcases List.mem_map.mp routeMem with
    ⟨taggedEdge, edgeMem, routeEq⟩
  have segmentMem :
      taggedSegment.1 ∈ gridPolylineSegments
        (constructedEdgeRoute graph taggedEdge.1 taggedEdge.2) := by
    rw [routeEq]
    exact List.fst_mem_of_mem_zipIdx taggedSegmentMem
  have edgeLocal : taggedEdge.1.span ≤ 1 :=
    isLocal taggedEdge.1 (List.fst_mem_of_mem_zipIdx edgeMem)
  exact (orthogonalPolyline_iff_segments _).mp
    (constructedEdgeRoute_orthogonal
      wellFormed degree edgeMem edgeLocal)
    taggedSegment.1 segmentMem

end PeriodicOrthocrossing
end LeanTrominoes
