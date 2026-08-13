/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCorrectness

/-!
# Port bookkeeping for the periodic track construction

Every edge end must receive a distinct port column.  This file proves that
the executable grouping by protovertex has exactly that property under the
maximum-degree-three premise.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- Edge index and endpoint kind uniquely identify a syntactic port. -/
def portKey {Vertex : Type*} (port : GraphPort Vertex) : Nat × PortEnd :=
  (port.edgeIndex, port.endKind)

/-- Expand every edge index into its source and target endpoint keys. -/
def portKeys (indices : List Nat) : List (Nat × PortEnd) :=
  indices.flatMap fun index => [(index, .source), (index, .target)]

@[simp]
theorem mem_portKeys_iff (index : Nat) (endKind : PortEnd)
    (indices : List Nat) :
    (index, endKind) ∈ portKeys indices ↔ index ∈ indices := by
  induction indices with
  | nil => simp [portKeys]
  | cons head rest induction =>
      cases endKind <;> simp [portKeys]

theorem portKeys_nodup {indices : List Nat} (indicesNodup : indices.Nodup) :
    (portKeys indices).Nodup := by
  induction indices with
  | nil => simp [portKeys]
  | cons head rest induction =>
      rw [List.nodup_cons] at indicesNodup
      simp only [portKeys, List.flatMap_cons]
      rw [List.nodup_append]
      refine ⟨by simp, induction indicesNodup.2, ?_⟩
      intro first firstMem second secondMem equal
      simp only [List.mem_cons, List.not_mem_nil, or_false] at firstMem
      rcases firstMem with rfl | rfl
      · apply indicesNodup.1
        apply (mem_portKeys_iff head .source rest).mp
        rw [equal]
        exact secondMem
      · apply indicesNodup.1
        apply (mem_portKeys_iff head .target rest).mp
        rw [equal]
        exact secondMem

theorem allPorts_map_key {Vertex : Type*} (graph : PeriodicGraph Vertex) :
    (allPorts graph).map portKey =
      portKeys (graph.edges.zipIdx.map Prod.snd) := by
  unfold allPorts portKeys
  rw [List.map_flatMap, List.flatMap_map]
  rfl

/-- All syntactic edge-end ports are pairwise distinct, even when the graph
contains repeated or parallel protoedges. -/
theorem allPorts_nodup {Vertex : Type*} (graph : PeriodicGraph Vertex) :
    (allPorts graph).Nodup := by
  apply List.Nodup.of_map portKey
  rw [allPorts_map_key]
  exact portKeys_nodup (List.nodup_zipIdx_map_snd graph.edges)

theorem portsAt_nodup {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (vertex : Vertex) :
    (portsAt graph vertex).Nodup :=
  (allPorts_nodup graph).filter _

theorem sourcePort_mem_allPorts {Vertex : Type*}
    (graph : PeriodicGraph Vertex)
    {taggedEdge : PeriodicEdge Vertex × Nat}
    (edgeMem : taggedEdge ∈ graph.edges.zipIdx) :
    sourcePort taggedEdge.1 taggedEdge.2 ∈ allPorts graph := by
  apply List.mem_flatMap.mpr
  exact ⟨taggedEdge, edgeMem, by simp [edgePorts, sourcePort]⟩

theorem targetPort_mem_allPorts {Vertex : Type*}
    (graph : PeriodicGraph Vertex)
    {taggedEdge : PeriodicEdge Vertex × Nat}
    (edgeMem : taggedEdge ∈ graph.edges.zipIdx) :
    targetPort taggedEdge.1 taggedEdge.2 ∈ allPorts graph := by
  apply List.mem_flatMap.mpr
  exact ⟨taggedEdge, edgeMem, by simp [edgePorts, targetPort]⟩

theorem sourcePort_mem_portsAt {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {taggedEdge : PeriodicEdge Vertex × Nat}
    (edgeMem : taggedEdge ∈ graph.edges.zipIdx) :
    sourcePort taggedEdge.1 taggedEdge.2 ∈
      portsAt graph taggedEdge.1.source := by
  apply List.mem_filter.mpr
  exact ⟨sourcePort_mem_allPorts graph edgeMem, by simp [sourcePort]⟩

theorem targetPort_mem_portsAt {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {taggedEdge : PeriodicEdge Vertex × Nat}
    (edgeMem : taggedEdge ∈ graph.edges.zipIdx) :
    targetPort taggedEdge.1 taggedEdge.2 ∈
      portsAt graph taggedEdge.1.target := by
  apply List.mem_filter.mpr
  exact ⟨targetPort_mem_allPorts graph edgeMem, by simp [targetPort]⟩

theorem allPorts_map_vertex {Vertex : Type*}
    (graph : PeriodicGraph Vertex) :
    (allPorts graph).map GraphPort.vertex = graph.incidences := by
  unfold allPorts PeriodicGraph.incidences
  rw [List.map_flatMap]
  simp only [edgePorts, List.map_cons, List.map_nil]
  exact PeriodicCNF.zipIdx_flatMap_fst
    PeriodicEdge.incidences graph.edges 0

theorem filter_length_eq_count_map {α β : Type*}
    [DecidableEq β] (function : α → β) (value : β)
    (values : List α) :
    (values.filter fun item => function item = value).length =
      (values.map function).count value := by
  induction values with
  | nil => rfl
  | cons head rest induction =>
      by_cases same : function head = value
      · simp [same, induction]
      · simp [same, induction]

/-- Grouping does not lose or duplicate incidences: the number of ports at a
vertex is its graph-theoretic degree. -/
theorem portsAt_length {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (vertex : Vertex) :
    (portsAt graph vertex).length =
      graph.incidences.count vertex := by
  unfold portsAt
  rw [filter_length_eq_count_map GraphPort.vertex vertex (allPorts graph),
    allPorts_map_vertex]

theorem port_vertex_mem {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} (wellFormed : graph.IsWellFormed)
    {port : GraphPort Vertex} (portMem : port ∈ allPorts graph) :
    port.vertex ∈ graph.vertices := by
  simp only [allPorts, List.mem_flatMap] at portMem
  rcases portMem with ⟨taggedEdge, edgeMem, portMem⟩
  have endpoints :=
    wellFormed.2 taggedEdge.1
      (List.fst_mem_of_mem_zipIdx edgeMem)
  simp only [edgePorts, List.mem_cons, List.not_mem_nil, or_false] at portMem
  rcases portMem with rfl | rfl
  · exact endpoints.1
  · exact endpoints.2

theorem port_mem_portsAt {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex)
    {port : GraphPort Vertex} (portMem : port ∈ allPorts graph) :
    port ∈ portsAt graph port.vertex := by
  simp [portsAt, portMem]

theorem portRank_lt_three {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} (degree : graph.DegreeAtMost 3)
    {port : GraphPort Vertex} (portMem : port ∈ allPorts graph) :
    portRank graph port < 3 := by
  have rankLt :
      portRank graph port < (portsAt graph port.vertex).length := by
    exact List.idxOf_lt_length_iff.mpr
      (port_mem_portsAt graph portMem)
  rw [portsAt_length] at rankLt
  exact Nat.lt_of_lt_of_le rankLt (degree port.vertex)

/-- Real ports have distinct columns.  Vertex blocks are eight columns
apart, while the three possible ranks occupy offsets `-2`, `0`, and `2`. -/
theorem portX_injective_on_allPorts {Vertex : Type*}
    [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    {first second : GraphPort Vertex}
    (firstMem : first ∈ allPorts graph)
    (secondMem : second ∈ allPorts graph)
    (sameX : portX graph first = portX graph second) :
    first = second := by
  have firstVertexMem := port_vertex_mem wellFormed firstMem
  have secondVertexMem := port_vertex_mem wellFormed secondMem
  have firstRankLt := portRank_lt_three degree firstMem
  have secondRankLt := portRank_lt_three degree secondMem
  have vertexIndexEqual :
      graph.vertices.idxOf first.vertex =
        graph.vertices.idxOf second.vertex := by
    unfold portX vertexX at sameX
    omega
  have rankEqual :
      portRank graph first = portRank graph second := by
    unfold portX vertexX at sameX
    omega
  have vertexEqual : first.vertex = second.vertex :=
    (List.idxOf_inj firstVertexMem).mp vertexIndexEqual
  have firstAt : first ∈ portsAt graph first.vertex :=
    port_mem_portsAt graph firstMem
  apply (List.idxOf_inj firstAt).mp
  unfold portRank at rankEqual
  simpa [vertexEqual] using rankEqual

/-- In particular, the two ends of one protoedge use different columns. -/
theorem sourcePortX_ne_targetPortX {Vertex : Type*}
    [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed)
    (degree : graph.DegreeAtMost 3)
    {taggedEdge : PeriodicEdge Vertex × Nat}
    (edgeMem : taggedEdge ∈ graph.edges.zipIdx) :
    portX graph (sourcePort taggedEdge.1 taggedEdge.2) ≠
      portX graph (targetPort taggedEdge.1 taggedEdge.2) := by
  intro sameX
  have samePort := portX_injective_on_allPorts wellFormed degree
    (sourcePort_mem_allPorts graph edgeMem)
    (targetPort_mem_allPorts graph edgeMem) sameX
  have endKindEqual := congrArg GraphPort.endKind samePort
  cases endKindEqual

end PeriodicOrthocrossing
end LeanTrominoes
