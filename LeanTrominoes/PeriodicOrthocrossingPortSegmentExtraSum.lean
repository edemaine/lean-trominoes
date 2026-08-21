/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListSumFiberPartition
import LeanTrominoes.PeriodicOrthocrossingHorizontalRouteSegmentCount
import LeanTrominoes.PeriodicOrthocrossingPorts

/-! # Total fanout segment extras

Port ranks enumerate each vertex's incident ports from zero.  Consequently,
the total number of noncentral fanout segments depends only on the finite
degree of each presented vertex.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- Number of noncentral fanout segments around a vertex of a given degree. -/
def portSegmentExtrasForDegree (degree : Nat) : Nat :=
  ((List.range degree).map portSegmentExtra).sum

@[simp] theorem portSegmentExtrasForDegree_zero :
    portSegmentExtrasForDegree 0 = 0 := rfl

@[simp] theorem portSegmentExtrasForDegree_one :
    portSegmentExtrasForDegree 1 = 1 := rfl

@[simp] theorem portSegmentExtrasForDegree_two :
    portSegmentExtrasForDegree 2 = 1 := rfl

@[simp] theorem portSegmentExtrasForDegree_three :
    portSegmentExtrasForDegree 3 = 2 := rfl

theorem portsAt_portSegmentExtra_sum {Vertex : Type*}
    [DecidableEq Vertex] (graph : PeriodicGraph Vertex) (vertex : Vertex) :
    ((portsAt graph vertex).map fun port =>
      portSegmentExtra (portRank graph port)).sum =
        portSegmentExtrasForDegree (portsAt graph vertex).length := by
  have ranksEq :
      (portsAt graph vertex).map (fun port =>
          portSegmentExtra (portRank graph port)) =
        (portsAt graph vertex).map (fun port =>
          portSegmentExtra ((portsAt graph vertex).idxOf port)) := by
    apply List.map_congr_left
    intro port portMember
    have vertexEq : port.vertex = vertex := by
      simpa only [portsAt, List.mem_filter, decide_eq_true_eq] using
        (List.mem_filter.mp portMember).2
    unfold portRank
    rw [vertexEq]
  rw [ranksEq]
  unfold portSegmentExtrasForDegree
  calc
    ((portsAt graph vertex).map fun port =>
        portSegmentExtra ((portsAt graph vertex).idxOf port)).sum =
      (((portsAt graph vertex).map fun port =>
        (portsAt graph vertex).idxOf port).map portSegmentExtra).sum := by
          simp [List.map_map, Function.comp_def]
    _ = ((List.range (portsAt graph vertex).length).map
          portSegmentExtra).sum := by
      rw [List.map_idxOf_self_eq_range
        (portsAt graph vertex) (portsAt_nodup graph vertex)]

/-- Summing endpoint extras in edge order is the same as summing the degree
contribution at every presented vertex. -/
theorem allPorts_portSegmentExtra_sum_eq_vertices
    {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} (wellFormed : graph.IsWellFormed) :
    ((allPorts graph).map fun port =>
      portSegmentExtra (portRank graph port)).sum =
        (graph.vertices.map fun vertex =>
          portSegmentExtrasForDegree
            (portsAt graph vertex).length).sum := by
  calc
    ((allPorts graph).map fun port =>
        portSegmentExtra (portRank graph port)).sum =
      (graph.vertices.map fun vertex =>
        (((allPorts graph).filter fun port =>
          port.vertex = vertex).map fun port =>
            portSegmentExtra (portRank graph port)).sum).sum :=
      List.sum_map_eq_sum_fibers
        GraphPort.vertex
        (fun port => portSegmentExtra (portRank graph port))
        (allPorts graph) graph.vertices wellFormed.1
        (fun port portMember =>
          port_vertex_mem wellFormed portMember)
    _ = (graph.vertices.map fun vertex =>
          portSegmentExtrasForDegree
            (portsAt graph vertex).length).sum := by
      congr 1
      apply List.map_congr_left
      intro vertex vertexMember
      exact portsAt_portSegmentExtra_sum graph vertex

/-- The all-port enumeration is exactly the source/target contribution of
each indexed edge. -/
theorem allPorts_portSegmentExtra_sum_eq_edges
    {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) :
    ((allPorts graph).map fun port =>
      portSegmentExtra (portRank graph port)).sum =
        (graph.edges.zipIdx.map fun tagged =>
          portSegmentExtra
              (portRank graph (sourcePort tagged.1 tagged.2)) +
            portSegmentExtra
              (portRank graph (targetPort tagged.1 tagged.2))).sum := by
  unfold allPorts
  generalize graph.edges.zipIdx = indexedEdges
  induction indexedEdges with
  | nil => rfl
  | cons tagged indexedEdges induction =>
      simp [edgePorts, sourcePort, targetPort, induction]
      omega

end PeriodicOrthocrossing
end LeanTrominoes
