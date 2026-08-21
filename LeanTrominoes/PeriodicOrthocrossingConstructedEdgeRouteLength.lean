/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingConstruction

/-! # Exact length of a constructed orthocrossing route

This small interface isolates the list arithmetic behind the track
construction.  It lets later counting arguments reason about the three
route pieces without expanding the points of the complete drawing.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

@[simp] theorem fanout_length (centerX portColumn : Int) :
    (fanout centerX portColumn).length =
      if centerX = portColumn then 2 else 3 := by
  by_cases same : centerX = portColumn <;> simp [fanout, same]

theorem edgeCore_length_ge_two_for_count {Vertex : Type*}
    [DecidableEq Vertex] (graph : PeriodicGraph Vertex)
    (edge : PeriodicEdge Vertex) (edgeIndex : Nat) :
    2 <= (edgeCore graph edge edgeIndex).length := by
  unfold edgeCore
  split <;> simp_all
  all_goals split <;> simp_all

theorem constructedEdgeRoute_length {Vertex : Type*}
    [DecidableEq Vertex] (graph : PeriodicGraph Vertex)
    (edge : PeriodicEdge Vertex) (edgeIndex : Nat) :
    (constructedEdgeRoute graph edge edgeIndex).length + 2 =
      (fanout
          (vertexX (graph.vertices.idxOf edge.source))
          (portX graph (sourcePort edge edgeIndex))).length +
        (edgeCore graph edge edgeIndex).length +
        (fanout
          (vertexX (graph.vertices.idxOf edge.target))
          (portX graph (targetPort edge edgeIndex))).length := by
  unfold constructedEdgeRoute joinPolylines translatePolyline
  simp only [List.length_append, List.length_tail, List.length_map,
    List.length_reverse]
  have coreLong : 2 <= (edgeCore graph edge edgeIndex).length :=
    edgeCore_length_ge_two_for_count graph edge edgeIndex
  have targetLong :
      2 <= (fanout
        (vertexX (graph.vertices.idxOf edge.target))
        (portX graph (targetPort edge edgeIndex))).length :=
    fanout_length_ge_two _ _
  omega

/-- The number of segments is the sum of the three component point counts,
minus the three shared/end points. -/
theorem constructedEdgeRoute_segments_length {Vertex : Type*}
    [DecidableEq Vertex] (graph : PeriodicGraph Vertex)
    (edge : PeriodicEdge Vertex) (edgeIndex : Nat) :
    (gridPolylineSegments
        (constructedEdgeRoute graph edge edgeIndex)).length + 3 =
      (fanout
          (vertexX (graph.vertices.idxOf edge.source))
          (portX graph (sourcePort edge edgeIndex))).length +
        (edgeCore graph edge edgeIndex).length +
        (fanout
          (vertexX (graph.vertices.idxOf edge.target))
          (portX graph (targetPort edge edgeIndex))).length := by
  rw [gridPolylineSegments_length]
  have routeLength :=
    constructedEdgeRoute_length graph edge edgeIndex
  have sourceLong :
      2 <= (fanout
        (vertexX (graph.vertices.idxOf edge.source))
        (portX graph (sourcePort edge edgeIndex))).length :=
    fanout_length_ge_two _ _
  have coreLong : 2 <= (edgeCore graph edge edgeIndex).length :=
    edgeCore_length_ge_two_for_count graph edge edgeIndex
  omega

end PeriodicOrthocrossing
end LeanTrominoes
