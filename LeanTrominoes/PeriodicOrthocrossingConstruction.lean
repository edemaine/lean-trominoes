import LeanTrominoes.PeriodicGridDrawing
import Mathlib.Data.List.GetD

/-!
# Track construction for periodic orthocrossing drawings

This is the discrete version of the routing construction in Theorem 2.1.
Each protovertex receives an eight-column block.  Its at-most-three incident
edge ends use three distinct port columns.  Every protoedge receives private
horizontal track rows, and vertically crossing edges use a private gate
column.  Neighbor-cell edges are routed across the appropriate boundary with
two track heights when necessary, preventing overlap with a translated copy.

The definitions in this file are deliberately executable.  Subsequent files
prove route compatibility and the orthocrossing invariant.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- Which endpoint of a protoedge one port represents. -/
inductive PortEnd
  | source
  | target
  deriving DecidableEq, Repr

/-- One edge-end occurrence, retaining both its protovertex and edge index. -/
structure GraphPort (Vertex : Type*) where
  vertex : Vertex
  edgeIndex : Nat
  endKind : PortEnd
  deriving DecidableEq, Repr

/-- The two ports contributed by one indexed protoedge. -/
def edgePorts {Vertex : Type*}
    (taggedEdge : PeriodicEdge Vertex × Nat) : List (GraphPort Vertex) :=
  [⟨taggedEdge.1.source, taggedEdge.2, .source⟩,
    ⟨taggedEdge.1.target, taggedEdge.2, .target⟩]

/-- All edge-end occurrences in edge-presentation order. -/
def allPorts {Vertex : Type*}
    (graph : PeriodicGraph Vertex) : List (GraphPort Vertex) :=
  graph.edges.zipIdx.flatMap edgePorts

/-- The ports incident to one protovertex, in edge-presentation order. -/
def portsAt {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (vertex : Vertex) :
    List (GraphPort Vertex) :=
  (allPorts graph).filter fun port => port.vertex = vertex

/-- Side length of the integer-scaled fundamental square.  The generous
constant leaves disjoint bands for vertex blocks, gate columns, and edge
tracks while remaining linear in presentation size. -/
def drawingGridSize {Vertex : Type*} (graph : PeriodicGraph Vertex) : Nat :=
  16 * (graph.vertices.length + graph.edges.length + 1)

/-- Center column of a protovertex's eight-column block. -/
def vertexX (vertexIndex : Nat) : Int :=
  8 * vertexIndex + 4

/-- Center position of one protovertex. -/
def vertexPosition (vertexIndex : Nat) : Cell :=
  (vertexX vertexIndex, 2)

/-- Rank of a port among the ports of its protovertex. -/
def portRank {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (port : GraphPort Vertex) : Nat :=
  (portsAt graph port.vertex).idxOf port

/-- Port columns are the left, center, and right columns of a vertex block.
The maximum-degree-three premise later proves that every real port uses one
of these three values. -/
def portX {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (port : GraphPort Vertex) : Int :=
  vertexX (graph.vertices.idxOf port.vertex) +
    2 * (portRank graph port : Int) - 2

/-- Grid point of one port before translating its whole lattice cell. -/
def portPosition {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (port : GraphPort Vertex) : Cell :=
  (portX graph port, 3)

/-- Private lower track row of one protoedge. -/
def edgeTrack (edgeIndex : Nat) : Int :=
  6 + 4 * edgeIndex

/-- Private gate column for a protoedge that changes vertical lattice cell. -/
def edgeGateX {Vertex : Type*}
    (graph : PeriodicGraph Vertex) (edgeIndex : Nat) : Int :=
  8 * graph.vertices.length + 4 + 2 * edgeIndex

/-- Concatenate two polylines known to share their boundary point, retaining
that point just once. -/
def joinPolylines (first second : List Cell) : List Cell :=
  first ++ second.tail

theorem joinPolylines_ne_nil_of_first
    {first second : List Cell} (firstNonempty : first ≠ []) :
    joinPolylines first second ≠ [] := by
  simp [joinPolylines, firstNonempty]

theorem joinPolylines_head?_of_first
    {first second : List Cell} (firstNonempty : first ≠ []) :
    (joinPolylines first second).head? = first.head? := by
  cases first with
  | nil => exact (firstNonempty rfl).elim
  | cons head rest => simp [joinPolylines]

theorem joinPolylines_getLast?_of_second
    {first second : List Cell} (secondLong : 2 ≤ second.length) :
    (joinPolylines first second).getLast? = second.getLast? := by
  cases second with
  | nil => simp at secondLong
  | cons head tail =>
      cases tail with
      | nil => simp at secondLong
      | cons next rest =>
          unfold joinPolylines
          change (first ++ (next :: rest)).getLast? =
            (head :: next :: rest).getLast?
          rw [List.getLast?_append_of_ne_nil first (by simp)]
          rw [List.getLast?_cons_cons]

/-- Orthogonal fanout from a vertex center to one of its three ports. -/
def fanout (centerX portColumn : Int) : List Cell :=
  if centerX = portColumn then
    [(centerX, 2), (portColumn, 3)]
  else
    [(centerX, 2), (portColumn, 2), (portColumn, 3)]

theorem fanout_ne_nil (centerX portColumn : Int) :
    fanout centerX portColumn ≠ [] := by
  by_cases same : centerX = portColumn <;> simp [fanout, same]

theorem fanout_length_ge_two (centerX portColumn : Int) :
    2 ≤ (fanout centerX portColumn).length := by
  by_cases same : centerX = portColumn <;> simp [fanout, same]

/-- Translate every point of a polyline. -/
def translatePolyline (offset : Cell) (points : List Cell) : List Cell :=
  points.map (Cell.add offset)

@[simp]
theorem translatePolyline_zero (points : List Cell) :
    translatePolyline (0, 0) points = points := by
  induction points with
  | nil => rfl
  | cons point points induction =>
      change List.map (Cell.add (0, 0)) points = points at induction
      simp only [translatePolyline, List.map_cons]
      rw [induction]
      simp [Cell.add]

/-- The port at the source end of one indexed edge. -/
def sourcePort {Vertex : Type*}
    (edge : PeriodicEdge Vertex) (edgeIndex : Nat) : GraphPort Vertex :=
  ⟨edge.source, edgeIndex, .source⟩

/-- The port at the target end of one indexed edge. -/
def targetPort {Vertex : Type*}
    (edge : PeriodicEdge Vertex) (edgeIndex : Nat) : GraphPort Vertex :=
  ⟨edge.target, edgeIndex, .target⟩

/-- Central track-to-track portion of one edge route.  The five local offset
cases are exactly those allowed by graph locality. -/
def edgeCore {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (edge : PeriodicEdge Vertex) (edgeIndex : Nat) : List Cell :=
  let size : Int := drawingGridSize graph
  let sourceX := portX graph (sourcePort edge edgeIndex)
  let targetX := portX graph (targetPort edge edgeIndex)
  let sourcePoint : Cell := (sourceX, 3)
  let targetPoint : Cell :=
    Cell.add (targetX, 3) (Cell.scale size edge.offset)
  let low := edgeTrack edgeIndex
  let high := low + 1
  let gate := edgeGateX graph edgeIndex
  match edge.offset with
  | (0, 0) =>
      [sourcePoint, (sourceX, low), (targetX, low), targetPoint]
  | (1, 0) =>
      if targetX < sourceX then
        [sourcePoint, (sourceX, low), (size + targetX, low), targetPoint]
      else
        [sourcePoint, (sourceX, low), (size, low), (size, high),
          (size + targetX, high), targetPoint]
  | (-1, 0) =>
      if sourceX < targetX then
        [sourcePoint, (sourceX, low), (targetX - size, low), targetPoint]
      else
        [sourcePoint, (sourceX, low), (0, low), (0, high),
          (targetX - size, high), targetPoint]
  | (0, 1) =>
      [sourcePoint, (sourceX, high), (gate, high), (gate, size + low),
        (targetX, size + low), targetPoint]
  | (0, -1) =>
      [sourcePoint, (sourceX, low), (gate, low), (gate, high - size),
        (targetX, high - size), targetPoint]
  | _ =>
      [sourcePoint, (sourceX, low), (targetPoint.1, low), targetPoint]

/-- Complete route from source vertex center, through its port and the edge
tracks, to the translated target vertex center. -/
def constructedEdgeRoute {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (edge : PeriodicEdge Vertex) (edgeIndex : Nat) : List Cell :=
  let sourceCenter :=
    vertexX (graph.vertices.idxOf edge.source)
  let targetCenter :=
    vertexX (graph.vertices.idxOf edge.target)
  let sourceColumn :=
    portX graph (sourcePort edge edgeIndex)
  let targetColumn :=
    portX graph (targetPort edge edgeIndex)
  let targetTranslate :=
    Cell.scale (drawingGridSize graph : Int) edge.offset
  let sourceFanout := fanout sourceCenter sourceColumn
  let targetFanout :=
    translatePolyline targetTranslate
      (fanout targetCenter targetColumn).reverse
  joinPolylines
    (joinPolylines sourceFanout (edgeCore graph edge edgeIndex))
    targetFanout

@[simp]
theorem constructedEdgeRoute_head? {Vertex : Type*}
    [DecidableEq Vertex] (graph : PeriodicGraph Vertex)
    (edge : PeriodicEdge Vertex) (edgeIndex : Nat) :
    (constructedEdgeRoute graph edge edgeIndex).head? =
      some (vertexPosition (graph.vertices.idxOf edge.source)) := by
  unfold constructedEdgeRoute
  let sourceCenter := vertexX (graph.vertices.idxOf edge.source)
  let sourceColumn := portX graph (sourcePort edge edgeIndex)
  have sourceNonempty : fanout sourceCenter sourceColumn ≠ [] :=
    fanout_ne_nil sourceCenter sourceColumn
  have innerNonempty :
      joinPolylines (fanout sourceCenter sourceColumn)
        (edgeCore graph edge edgeIndex) ≠ [] :=
    joinPolylines_ne_nil_of_first sourceNonempty
  rw [joinPolylines_head?_of_first innerNonempty,
    joinPolylines_head?_of_first sourceNonempty]
  by_cases same : sourceCenter = sourceColumn
  · simp [fanout, same, vertexPosition, sourceCenter]
  · simp [fanout, same, vertexPosition, sourceCenter]

@[simp]
theorem constructedEdgeRoute_getLast? {Vertex : Type*}
    [DecidableEq Vertex] (graph : PeriodicGraph Vertex)
    (edge : PeriodicEdge Vertex) (edgeIndex : Nat) :
    (constructedEdgeRoute graph edge edgeIndex).getLast? =
      some (Cell.add
        (vertexPosition (graph.vertices.idxOf edge.target))
        (Cell.scale (drawingGridSize graph : Int) edge.offset)) := by
  unfold constructedEdgeRoute
  let targetCenter := vertexX (graph.vertices.idxOf edge.target)
  let targetColumn := portX graph (targetPort edge edgeIndex)
  let targetTranslate :=
    Cell.scale (drawingGridSize graph : Int) edge.offset
  have targetLong :
      2 ≤ (translatePolyline targetTranslate
        (fanout targetCenter targetColumn).reverse).length := by
    simp only [translatePolyline, List.length_map, List.length_reverse]
    exact fanout_length_ge_two targetCenter targetColumn
  rw [joinPolylines_getLast?_of_second targetLong]
  by_cases same : targetCenter = targetColumn
  · simp [translatePolyline, fanout, same, vertexPosition, targetCenter,
      targetTranslate, Cell.add, add_comm]
  · simp [translatePolyline, fanout, same, vertexPosition, targetCenter,
      targetTranslate, Cell.add, add_comm]

/-- Vertex positions in protovertex-presentation order. -/
def constructedVertexPositions {Vertex : Type*}
    (graph : PeriodicGraph Vertex) : List Cell :=
  graph.vertices.zipIdx.map fun tagged =>
    vertexPosition tagged.2

/-- Edge routes in protoedge-presentation order. -/
def constructedEdgeRoutes {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) : List (List Cell) :=
  graph.edges.zipIdx.map fun tagged =>
    constructedEdgeRoute graph tagged.1 tagged.2

/-- Executable track drawing associated with a periodic graph presentation. -/
def drawing {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) : PeriodicGridDrawing where
  gridSizePred := drawingGridSize graph - 1
  vertexPositions := constructedVertexPositions graph
  edgeRoutes := constructedEdgeRoutes graph

theorem drawingGridSize_pos {Vertex : Type*}
    (graph : PeriodicGraph Vertex) :
    0 < drawingGridSize graph := by
  unfold drawingGridSize
  omega

@[simp]
theorem drawing_gridSize {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    (drawing graph).gridSize = drawingGridSize graph := by
  unfold drawing PeriodicGridDrawing.gridSize
  change drawingGridSize graph - 1 + 1 = drawingGridSize graph
  have positive := drawingGridSize_pos graph
  omega

@[simp]
theorem constructedVertexPositions_length {Vertex : Type*}
    (graph : PeriodicGraph Vertex) :
    (constructedVertexPositions graph).length = graph.vertices.length := by
  simp [constructedVertexPositions]

@[simp]
theorem constructedEdgeRoutes_length {Vertex : Type*}
    [DecidableEq Vertex] (graph : PeriodicGraph Vertex) :
    (constructedEdgeRoutes graph).length = graph.edges.length := by
  simp [constructedEdgeRoutes]

@[simp]
theorem drawing_vertexPositions_length {Vertex : Type*}
    [DecidableEq Vertex] (graph : PeriodicGraph Vertex) :
    (drawing graph).vertexPositions.length = graph.vertices.length :=
  constructedVertexPositions_length graph

@[simp]
theorem drawing_edgeRoutes_length {Vertex : Type*}
    [DecidableEq Vertex] (graph : PeriodicGraph Vertex) :
    (drawing graph).edgeRoutes.length = graph.edges.length :=
  constructedEdgeRoutes_length graph

end PeriodicOrthocrossing
end LeanTrominoes
