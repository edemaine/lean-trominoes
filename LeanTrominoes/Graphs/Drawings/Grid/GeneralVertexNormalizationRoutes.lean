/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.GeneralVertexNormalizationFanGeometry
import LeanTrominoes.Common.Geometry.GridPolylineScaledEndpointTrimEndpoints
import LeanTrominoes.Common.Geometry.GridPolylineScaledEndpointTrimTranslation
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingVertexCoverage

/-! # The normalized route consists of two vertex fans and a trimmed core -/
namespace LeanTrominoes.GeneralVertexNormalization
open PeriodicOrthocrossing

def liftedVertex {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex)
    (drawing : PeriodicGridDrawing) (vertex : Vertex) (cell : Cell) : Cell :=
  Cell.add (drawing.vertexPosition graph vertex) (drawing.periodTranslation cell)

def sourceFan {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (chosen : Vertex → GraphPort Vertex) (tagged : PeriodicEdge Vertex × Nat) (cell : Cell) : List Cell :=
  fanAt graph drawing chosen (sourcePort tagged.1 tagged.2) (liftedVertex graph drawing tagged.1.source cell)

def targetFan {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (chosen : Vertex → GraphPort Vertex) (tagged : PeriodicEdge Vertex × Nat) (cell : Cell) : List Cell :=
  fanAt graph drawing chosen (targetPort tagged.1 tagged.2)
    (liftedVertex graph drawing tagged.1.target (Cell.add cell tagged.1.offset))

def trimmedCore (drawing : PeriodicGridDrawing) (index : Nat) (cell : Cell) : List Cell :=
  GridPolyline.clippedScaledRoute (drawing.realEdgeRoute index cell)

def normalizedRoute {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (chosen : Vertex → GraphPort Vertex) (tagged : PeriodicEdge Vertex × Nat) (cell : Cell) : List Cell :=
  joinPolylines (joinPolylines (sourceFan graph drawing chosen tagged cell) (trimmedCore drawing tagged.2 cell))
    (targetFan graph drawing chosen tagged cell).reverse

variable {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}

theorem liftedRoute_simple (valid : drawing.IsRealDrawing graph) {tagged : PeriodicEdge Vertex × Nat}
    (member : tagged ∈ graph.edges.zipIdx) (cell : Cell) :
    GridPolyline.IsRealSimple (drawing.realEdgeRoute tagged.2 cell) :=
  (valid.2.1 _ (PeriodicGridDrawing.edgeRoute_mem_of_compatible valid.1 member)).translate _

theorem liftedRoute_orthogonal (valid : drawing.IsCompatible graph) (orthogonal : drawing.IsOrthogonal)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx) (cell : Cell) :
    OrthogonalPolyline (drawing.realEdgeRoute tagged.2 cell) :=
  ((PeriodicGridDrawing.isOrthogonal_iff_routes _).mp orthogonal _
    (PeriodicGridDrawing.edgeRoute_mem_of_compatible valid member)).translate _

theorem liftedRoute_endpoints (valid : drawing.IsCompatible graph) {tagged : PeriodicEdge Vertex × Nat}
    (member : tagged ∈ graph.edges.zipIdx) (cell : Cell) :
    (drawing.realEdgeRoute tagged.2 cell).head? = some (liftedVertex graph drawing tagged.1.source cell) ∧
    (drawing.realEdgeRoute tagged.2 cell).getLast? =
      some (liftedVertex graph drawing tagged.1.target (Cell.add cell tagged.1.offset)) := by
  have routeMatches := valid.2.2.2.2.2 tagged member
  constructor
  · simpa [PeriodicGridDrawing.realEdgeRoute,List.head?_map,routeMatches.1,liftedVertex,Cell.add,add_comm]
  · rw [PeriodicGridDrawing.realEdgeRoute,List.getLast?_map,routeMatches.2]
    simp only [Option.map_some,Option.some.injEq]
    apply Prod.ext <;> simp [liftedVertex,PeriodicGridDrawing.periodTranslation,Cell.add,Cell.scale] <;> ring

theorem liftedRoute_vertexAvoidance (valid : drawing.IsRealDrawing graph) {tagged : PeriodicEdge Vertex × Nat}
    (member : tagged ∈ graph.edges.zipIdx) {vertex : Vertex} (vertexMember : vertex ∈ graph.vertices)
    (vertexCell edgeCell : Cell) :
    GridPolyline.RealContains (drawing.realEdgeRoute tagged.2 edgeCell) (realCell (liftedVertex graph drawing vertex vertexCell)) →
      GridPolyline.RealIsEndpoint (drawing.realEdgeRoute tagged.2 edgeCell) (realCell (liftedVertex graph drawing vertex vertexCell)) := by
  apply valid.2.2 _ (valid.1.vertexPosition_mem vertexMember) vertexCell edgeCell tagged.2
  rw [valid.1.2.2.1]
  exact List.snd_lt_of_mem_zipIdx member

theorem fanAt_head (chosen : Vertex → GraphPort Vertex) (port : GraphPort Vertex) (position : Cell) :
    (fanAt graph drawing chosen port position).head? = some (Cell.scale 32 position) := by
  simp [fanAt,translatePolyline,List.head?_map,fanAssignment_head,Cell.add]

theorem fanAt_last (distinct : DistinctPortSides drawing graph) (chosen : Vertex → GraphPort Vertex)
    {port : GraphPort Vertex} (member : port ∈ allPorts graph) (position : Cell) :
    (fanAt graph drawing chosen port position).getLast? =
      some (Cell.add (Cell.scale 32 position) (Cell.scale 8 (portSide drawing port).direction.step)) := by
  rw [fanAt,translatePolyline,List.getLast?_map,fanAssignment_last distinct chosen member]
  rfl

theorem sourceFan_joint (valid : drawing.IsRealDrawing graph) (orthogonal : drawing.IsOrthogonal)
    (distinct : DistinctPortSides drawing graph) (chosen : Vertex → GraphPort Vertex)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx) (cell : Cell) :
    (sourceFan graph drawing chosen tagged cell).getLast? = (trimmedCore drawing tagged.2 cell).head? := by
  have oldSimple := liftedRoute_simple valid member cell
  have ends := liftedRoute_endpoints valid.1 member cell
  rw [sourceFan,fanAt_last distinct chosen (sourcePort_mem_allPorts graph member),trimmedCore,
    GridPolyline.clippedScaledRoute_head oldSimple.1 ends.1,
    portSide_direction valid orthogonal (sourcePort_mem_allPorts graph member)]
  have direction : AxisDirection.polylineFirstDirection (drawing.realEdgeRoute tagged.2 cell) =
      AxisDirection.polylineFirstDirection (drawing.edgeRoute tagged.2) :=
    AxisDirection.polylineFirstDirection_translatePolyline _ _
  simpa only [portDirection,sourcePort,direction]

theorem targetFan_joint (valid : drawing.IsRealDrawing graph) (orthogonal : drawing.IsOrthogonal)
    (distinct : DistinctPortSides drawing graph) (chosen : Vertex → GraphPort Vertex)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx) (cell : Cell) :
    (trimmedCore drawing tagged.2 cell).getLast? = (targetFan graph drawing chosen tagged cell).reverse.head? := by
  have oldSimple := liftedRoute_simple valid member cell
  have oldOrthogonal := liftedRoute_orthogonal valid.1 orthogonal member cell
  have ends := liftedRoute_endpoints valid.1 member cell
  rw [List.head?_reverse,targetFan,fanAt_last distinct chosen (targetPort_mem_allPorts graph member),trimmedCore,
    GridPolyline.clippedScaledRoute_last oldSimple.1 oldOrthogonal ends.2,
    portSide_direction valid orthogonal (targetPort_mem_allPorts graph member)]
  have direction : AxisDirection.polylineLastDirection (drawing.realEdgeRoute tagged.2 cell) =
      AxisDirection.polylineLastDirection (drawing.edgeRoute tagged.2) :=
    AxisDirection.polylineLastDirection_translatePolyline _ _
  simpa only [portDirection,targetPort,direction]

theorem normalizedRoute_segments (valid : drawing.IsRealDrawing graph) (orthogonal : drawing.IsOrthogonal)
    (distinct : DistinctPortSides drawing graph) (chosen : Vertex → GraphPort Vertex)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx) (cell : Cell) :
    gridPolylineSegments (normalizedRoute graph drawing chosen tagged cell) =
      (gridPolylineSegments (sourceFan graph drawing chosen tagged cell) ++
        gridPolylineSegments (trimmedCore drawing tagged.2 cell)) ++
      gridPolylineSegments (targetFan graph drawing chosen tagged cell).reverse := by
  have firstLast := fanAt_last distinct chosen (sourcePort_mem_allPorts graph member) (liftedVertex graph drawing tagged.1.source cell)
  have middleHead := (sourceFan_joint valid orthogonal distinct chosen member cell).symm.trans firstLast
  have middleLong := (liftedRoute_simple valid member cell).1
  have middleLast := fanAt_last distinct chosen (targetPort_mem_allPorts graph member)
    (liftedVertex graph drawing tagged.1.target (Cell.add cell tagged.1.offset))
  have lastHead : (targetFan graph drawing chosen tagged cell).reverse.head? =
      some (Cell.add (Cell.scale 32 (liftedVertex graph drawing tagged.1.target (Cell.add cell tagged.1.offset)))
        (Cell.scale 8 (portSide drawing (targetPort tagged.1 tagged.2)).direction.step)) := by
    rw [List.head?_reverse]
    exact middleLast
  have middleEnd := (targetFan_joint valid orthogonal distinct chosen member cell).trans lastHead
  have firstMiddleLast := joinPolylines_getLast?_of_second
    (first := sourceFan graph drawing chosen tagged cell) (second := trimmedCore drawing tagged.2 cell)
    (by simpa [trimmedCore,GridPolyline.clippedScaledRoute_length,
    PeriodicGridDrawing.realEdgeRoute] using middleLong)
  unfold normalizedRoute
  rw [gridPolylineSegments_joinPolylines (firstMiddleLast.trans middleEnd) lastHead,
    gridPolylineSegments_joinPolylines (first := sourceFan graph drawing chosen tagged cell) firstLast middleHead]

theorem normalizedRoute_realContains_parts (valid : drawing.IsRealDrawing graph) (orthogonal : drawing.IsOrthogonal)
    (distinct : DistinctPortSides drawing graph) (chosen : Vertex → GraphPort Vertex)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx) (cell : Cell) (point : ℝ × ℝ) :
    GridPolyline.RealContains (normalizedRoute graph drawing chosen tagged cell) point ↔
      (GridPolyline.RealContains (sourceFan graph drawing chosen tagged cell) point ∨
        GridPolyline.RealContains (trimmedCore drawing tagged.2 cell) point) ∨
      GridPolyline.RealContains (targetFan graph drawing chosen tagged cell) point := by
  unfold GridPolyline.RealContains
  rw [normalizedRoute_segments valid orthogonal distinct chosen member cell]
  simp only [List.mem_append,or_and_right,exists_or]
  rw [show (∃ segment ∈ gridPolylineSegments (targetFan graph drawing chosen tagged cell).reverse,
      segment.RealContains point) ↔ GridPolyline.RealContains (targetFan graph drawing chosen tagged cell) point from
    GridPolyline.realContains_reverse _ _]
  rfl

end LeanTrominoes.GeneralVertexNormalization
