/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingConstructedEdgeRouteLength

/-! # Segment counts for horizontal local routes

For the CNF drawings used by the strip reduction, clause anchors make every
incidence offset horizontal.  Once the target port is known to lie left of
the source port, a route has five baseline segments, one extra segment at
each noncentral port, and two extra segments precisely for offset `(-1, 0)`.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- A noncentral rank needs one horizontal fanout segment. -/
def portSegmentExtra (rank : Nat) : Nat :=
  if rank = 1 then 0 else 1

/-- A left-wrapping horizontal core needs the two boundary-detour segments. -/
def backwardCoreSegmentExtra (offset : Cell) : Nat :=
  if offset = (-1, 0) then 2 else 0

theorem sourceFanout_length_eq_two_add_extra {Vertex : Type*}
    [DecidableEq Vertex] (graph : PeriodicGraph Vertex)
    (edge : PeriodicEdge Vertex) (edgeIndex : Nat) :
    (fanout
        (vertexX (graph.vertices.idxOf edge.source))
        (portX graph (sourcePort edge edgeIndex))).length =
      2 + portSegmentExtra
        (portRank graph (sourcePort edge edgeIndex)) := by
  rw [fanout_length]
  unfold portSegmentExtra portX sourcePort
  by_cases central :
      portRank graph
        { vertex := edge.source, edgeIndex := edgeIndex,
          endKind := PortEnd.source } = 1
  · simp [central]
  · have notSame :
        vertexX (graph.vertices.idxOf edge.source) ≠
          vertexX (graph.vertices.idxOf edge.source) +
            2 * (portRank graph
              { vertex := edge.source, edgeIndex := edgeIndex,
                endKind := PortEnd.source } : Int) - 2 := by
      unfold vertexX
      omega
    simp [central, notSame]

theorem targetFanout_length_eq_two_add_extra {Vertex : Type*}
    [DecidableEq Vertex] (graph : PeriodicGraph Vertex)
    (edge : PeriodicEdge Vertex) (edgeIndex : Nat) :
    (fanout
        (vertexX (graph.vertices.idxOf edge.target))
        (portX graph (targetPort edge edgeIndex))).length =
      2 + portSegmentExtra
        (portRank graph (targetPort edge edgeIndex)) := by
  rw [fanout_length]
  unfold portSegmentExtra portX targetPort
  by_cases central :
      portRank graph
        { vertex := edge.target, edgeIndex := edgeIndex,
          endKind := PortEnd.target } = 1
  · simp [central]
  · have notSame :
        vertexX (graph.vertices.idxOf edge.target) ≠
          vertexX (graph.vertices.idxOf edge.target) +
            2 * (portRank graph
              { vertex := edge.target, edgeIndex := edgeIndex,
                endKind := PortEnd.target } : Int) - 2 := by
      unfold vertexX
      omega
    simp [central, notSame]

theorem edgeCore_length_eq_four_add_backwardExtra
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (edge : PeriodicEdge Vertex) (edgeIndex : Nat)
    (horizontal : edge.offset = (0, 0) ∨
      edge.offset = (1, 0) ∨ edge.offset = (-1, 0))
    (targetLtSource :
      portX graph (targetPort edge edgeIndex) <
        portX graph (sourcePort edge edgeIndex)) :
    (edgeCore graph edge edgeIndex).length =
      4 + backwardCoreSegmentExtra edge.offset := by
  rcases horizontal with zero | right | left
  · simp [edgeCore, zero, backwardCoreSegmentExtra]
  · simp [edgeCore, right, targetLtSource, backwardCoreSegmentExtra]
  · have notSourceLtTarget :
        ¬(portX graph (sourcePort edge edgeIndex) <
          portX graph (targetPort edge edgeIndex)) := by
      omega
    simp [edgeCore, left, notSourceLtTarget,
      backwardCoreSegmentExtra]

/-- Closed per-route segment count used by the CNF presentation scan. -/
theorem constructedEdgeRoute_segments_length_horizontal
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    (edge : PeriodicEdge Vertex) (edgeIndex : Nat)
    (horizontal : edge.offset = (0, 0) ∨
      edge.offset = (1, 0) ∨ edge.offset = (-1, 0))
    (targetLtSource :
      portX graph (targetPort edge edgeIndex) <
        portX graph (sourcePort edge edgeIndex)) :
    (gridPolylineSegments
        (constructedEdgeRoute graph edge edgeIndex)).length =
      5 + portSegmentExtra
          (portRank graph (sourcePort edge edgeIndex)) +
        portSegmentExtra
          (portRank graph (targetPort edge edgeIndex)) +
        backwardCoreSegmentExtra edge.offset := by
  have pieces := constructedEdgeRoute_segments_length
    graph edge edgeIndex
  rw [sourceFanout_length_eq_two_add_extra,
    targetFanout_length_eq_two_add_extra,
    edgeCore_length_eq_four_add_backwardExtra
      graph edge edgeIndex horizontal targetLtSource] at pieces
  omega

end PeriodicOrthocrossing
end LeanTrominoes
