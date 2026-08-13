/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingPlanarRouteCore

/-!
# Route endpoints at lifted graph vertices

The complete route core treats each translated protoedge route as one Boolean
carrier.  To attach those carriers to SAT gadgets, we retain the protoedge,
its source/target role, and the corresponding first/last segment terminal.
The enumeration below covers the same neighboring `3 × 3` translate block as
the carrier and bend layers.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- One endpoint of one translated protoedge route, together with the
segment terminal that reaches the lifted graph vertex. -/
structure RouteEndpoint (Vertex : Type*) where
  edge : PeriodicEdge Vertex
  edgeIndex : Nat
  translate : Cell
  endKind : PortEnd
  terminal : SegmentTerminal
  deriving DecidableEq, Repr

/-- The route occurrence to which an endpoint belongs. -/
def RouteEndpoint.routeKey {Vertex : Type*}
    (endpoint : RouteEndpoint Vertex) : RouteOccurrenceKey :=
  (endpoint.edgeIndex, endpoint.translate)

/-- The lifted graph vertex reached by a route endpoint.  The target endpoint
is translated by the protoedge offset, exactly as in `PeriodicEdge.Connects`. -/
def RouteEndpoint.vertexOccurrence {Vertex : Type*}
    (endpoint : RouteEndpoint Vertex) : Vertex × Cell :=
  match endpoint.endKind with
  | .source => (endpoint.edge.source, endpoint.translate)
  | .target =>
      (endpoint.edge.target,
        Cell.add endpoint.translate endpoint.edge.offset)

/-- Regard the endpoint terminal as an external carrier node. -/
def RouteEndpoint.carrierNode {Vertex : Type*}
    (endpoint : RouteEndpoint Vertex) : CarrierNode :=
  .terminal endpoint.terminal

/-- Build the source and target endpoint records from the nonempty indexed
segment list of one route.  Empty routes contribute no endpoints. -/
def routeEndpointsFromSegments {Vertex : Type*}
    (edge : PeriodicEdge Vertex) (edgeIndex : Nat) (translate : Cell) :
    List (GridSegment × Nat) → List (RouteEndpoint Vertex)
  | [] => []
  | first :: rest =>
      let last := (first :: rest).getLastD first
      [⟨edge, edgeIndex, translate, .source,
          ⟨⟨edgeIndex, first.2, first.1⟩, translate, .start⟩⟩,
        ⟨edge, edgeIndex, translate, .target,
          ⟨⟨edgeIndex, last.2, last.1⟩, translate, .finish⟩⟩]

/-- Source and target endpoint records for one translated indexed
protoedge. -/
def translatedEdgeRouteEndpoints
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (taggedEdge : PeriodicEdge Vertex × Nat) (translate : Cell) :
    List (RouteEndpoint Vertex) :=
  routeEndpointsFromSegments taggedEdge.1 taggedEdge.2 translate
    (gridPolylineSegments
      (constructedEdgeRoute graph taggedEdge.1 taggedEdge.2)).zipIdx

/-- Every route endpoint in the neighboring `3 × 3` occurrence block. -/
def drawingRouteEndpoints
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) : List (RouteEndpoint Vertex) :=
  graph.edges.zipIdx.flatMap fun taggedEdge =>
    neighborTranslations.flatMap fun translate =>
      translatedEdgeRouteEndpoints graph taggedEdge translate

/-- Endpoint construction records the route index and translation directly
in its segment terminal. -/
theorem routeEndpointsFromSegments_terminal_routeKey
    {Vertex : Type*}
    (edge : PeriodicEdge Vertex) (edgeIndex : Nat) (translate : Cell)
    (segments : List (GridSegment × Nat))
    {endpoint : RouteEndpoint Vertex}
    (endpointMem :
      endpoint ∈
        routeEndpointsFromSegments edge edgeIndex translate segments) :
    endpoint.terminal.routeKey = endpoint.routeKey := by
  cases segments with
  | nil =>
      simp [routeEndpointsFromSegments] at endpointMem
  | cons first rest =>
      simp only [routeEndpointsFromSegments, List.mem_cons,
        List.not_mem_nil, or_false] at endpointMem
      rcases endpointMem with endpointEq | endpointEq <;>
        subst endpoint <;> rfl

/-- The endpoint record itself retains the requested route index and
translation. -/
theorem routeEndpointsFromSegments_routeKey
    {Vertex : Type*}
    (edge : PeriodicEdge Vertex) (edgeIndex : Nat) (translate : Cell)
    (segments : List (GridSegment × Nat))
    {endpoint : RouteEndpoint Vertex}
    (endpointMem :
      endpoint ∈
        routeEndpointsFromSegments edge edgeIndex translate segments) :
    endpoint.routeKey = (edgeIndex, translate) := by
  cases segments with
  | nil =>
      simp [routeEndpointsFromSegments] at endpointMem
  | cons first rest =>
      simp only [routeEndpointsFromSegments, List.mem_cons,
        List.not_mem_nil, or_false] at endpointMem
      rcases endpointMem with endpointEq | endpointEq <;>
        subst endpoint <;> rfl

/-- Every enumerated endpoint terminal stays on the translated protoedge
route named by its endpoint record. -/
theorem drawingRouteEndpoints_terminal_routeKey
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {endpoint : RouteEndpoint Vertex}
    (endpointMem : endpoint ∈ drawingRouteEndpoints graph) :
    endpoint.terminal.routeKey = endpoint.routeKey := by
  rcases List.mem_flatMap.mp endpointMem with
    ⟨taggedEdge, taggedEdgeMem, endpointMem⟩
  rcases List.mem_flatMap.mp endpointMem with
    ⟨translate, translateMem, endpointMem⟩
  exact routeEndpointsFromSegments_terminal_routeKey
    taggedEdge.1 taggedEdge.2 translate
    (gridPolylineSegments
      (constructedEdgeRoute graph taggedEdge.1 taggedEdge.2)).zipIdx
    endpointMem

/-- Both endpoint records exist for every constructed route. -/
theorem translatedEdgeRouteEndpoints_length
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (taggedEdge : PeriodicEdge Vertex × Nat) (translate : Cell) :
    (translatedEdgeRouteEndpoints graph taggedEdge translate).length = 2 := by
  have routeLong :
      2 ≤
        (constructedEdgeRoute graph taggedEdge.1 taggedEdge.2).length := by
    unfold constructedEdgeRoute joinPolylines
    simp only [List.length_append]
    have sourceLong :=
      fanout_length_ge_two
        (vertexX (graph.vertices.idxOf taggedEdge.1.source))
        (portX graph (sourcePort taggedEdge.1 taggedEdge.2))
    omega
  have segmentsNonempty :
      gridPolylineSegments
          (constructedEdgeRoute graph taggedEdge.1 taggedEdge.2) ≠ [] := by
    intro segmentsEmpty
    have lengthZero :=
      congrArg List.length segmentsEmpty
    rw [gridPolylineSegments_length] at lengthZero
    simp only [List.length_nil] at lengthZero
    omega
  unfold translatedEdgeRouteEndpoints
  cases segmentsEq :
      gridPolylineSegments
        (constructedEdgeRoute graph taggedEdge.1 taggedEdge.2) with
  | nil =>
      exact (segmentsNonempty segmentsEq).elim
  | cons first rest =>
      simp [routeEndpointsFromSegments]

end PeriodicOrthocrossing
end LeanTrominoes
