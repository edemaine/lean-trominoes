/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicOrthocrossingPorts
import LeanTrominoes.ListSumFiberPartition
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic

/-! # Linear-width vertex blocks for arbitrary degrees

Each vertex receives its degree plus three columns. The padding separates
the straight fans, including isolated vertices. All edge-end ports remain
distinct without a degree bound.
-/
namespace LeanTrominoes.PeriodicOrthocrossing.GeneralPorts

def degrees {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex) : List Nat :=
  graph.vertices.map fun vertex => (portsAt graph vertex).length

def blockStart (counts : List Nat) (index : Nat) : Nat :=
  2+(counts.take index).sum+3*index

theorem block_separated (counts : List Nat) {first second : Nat}
    (firstValid : first < counts.length) (ordered : first < second) :
    blockStart counts first+counts[first]+3 ≤ blockStart counts second := by
  have mono := List.monotone_sum_take counts (by omega : first+1 ≤ second)
  dsimp only at mono
  rw [List.sum_take_succ _ _ firstValid] at mono
  unfold blockStart
  omega

theorem block_within_total (counts : List Nat) {index : Nat} (valid : index < counts.length) :
    blockStart counts index+counts[index]+3 ≤ 2+counts.sum+3*counts.length := by
  have mono := List.monotone_sum_take counts (by omega : index+1 ≤ counts.length)
  dsimp only at mono
  rw [List.sum_take_succ _ _ valid,List.take_length] at mono
  unfold blockStart
  omega

theorem degrees_sum {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed) : (degrees graph).sum = 2*graph.edges.length := by
  have fibers := List.sum_map_eq_sum_fibers GraphPort.vertex (fun _ : GraphPort Vertex => 1)
    (allPorts graph) graph.vertices wellFormed.1 (fun port member => port_vertex_mem wellFormed member)
  have count : (allPorts graph).length = 2*graph.edges.length := by
    have general (edges : List (PeriodicEdge Vertex × Nat)) :
        (edges.flatMap edgePorts).length = 2*edges.length := by
      induction edges with
      | nil => simp
      | cons edge rest ih => simp [edgePorts,ih]; omega
    simpa [allPorts] using general graph.edges.zipIdx
  simpa [degrees,portsAt] using (fibers.symm.trans (by simpa using count))

def vertexX {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex) (vertex : Vertex) : Int :=
  blockStart (degrees graph) (graph.vertices.idxOf vertex)+1

def portX {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex) (port : GraphPort Vertex) : Int :=
  blockStart (degrees graph) (graph.vertices.idxOf port.vertex)+(portRank graph port : Nat)

private theorem degree_at_index {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {vertex : Vertex} (member : vertex ∈ graph.vertices) :
    (degrees graph)[graph.vertices.idxOf vertex]'(by simpa [degrees] using List.idxOf_lt_length_iff.mpr member) =
      (portsAt graph vertex).length := by
  simp [degrees,List.getElem_idxOf (List.idxOf_lt_length_iff.mpr member)]

theorem port_rank_bound {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {port : GraphPort Vertex} (member : port ∈ allPorts graph) :
    portRank graph port < (portsAt graph port.vertex).length := by
  exact List.idxOf_lt_length_iff.mpr (port_mem_portsAt graph member)

theorem ports_in_distinct_blocks {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed) {first second : GraphPort Vertex}
    (firstMember : first ∈ allPorts graph) (_secondMember : second ∈ allPorts graph)
    (ordered : graph.vertices.idxOf first.vertex < graph.vertices.idxOf second.vertex) :
    portX graph first+3 < portX graph second := by
  have member := port_vertex_mem wellFormed firstMember
  have valid : graph.vertices.idxOf first.vertex < (degrees graph).length := by
    simpa [degrees] using List.idxOf_lt_length_iff.mpr member
  have separation := block_separated (degrees graph) valid ordered
  rw [degree_at_index member] at separation
  have rank := port_rank_bound firstMember
  unfold portX
  exact_mod_cast (by omega :
    blockStart (degrees graph) (graph.vertices.idxOf first.vertex)+portRank graph first+3 <
      blockStart (degrees graph) (graph.vertices.idxOf second.vertex)+portRank graph second)

theorem portX_injective {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed) {first second : GraphPort Vertex}
    (firstMember : first ∈ allPorts graph) (secondMember : second ∈ allPorts graph)
    (equal : portX graph first = portX graph second) : first = second := by
  have firstVertex := port_vertex_mem wellFormed firstMember
  have secondVertex := port_vertex_mem wellFormed secondMember
  have indices : graph.vertices.idxOf first.vertex = graph.vertices.idxOf second.vertex := by
    rcases lt_trichotomy (graph.vertices.idxOf first.vertex) (graph.vertices.idxOf second.vertex) with lt | eq | gt
    · have separated := ports_in_distinct_blocks wellFormed firstMember secondMember lt
      omega
    · exact eq
    · have separated := ports_in_distinct_blocks wellFormed secondMember firstMember gt
      omega
  have vertices : first.vertex = second.vertex := (List.idxOf_inj firstVertex).mp indices
  have ranks : portRank graph first = portRank graph second := by
    unfold portX at equal
    rw [indices] at equal
    exact_mod_cast (Nat.add_left_cancel (by exact_mod_cast equal))
  apply (List.idxOf_inj (port_mem_portsAt graph firstMember)).mp
  simpa [portRank,vertices] using ranks

theorem portX_bounds {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed) {port : GraphPort Vertex}
    (member : port ∈ allPorts graph) :
    0 < portX graph port ∧ portX graph port < 3*graph.vertices.length+2*graph.edges.length+2 := by
  have vertexMember := port_vertex_mem wellFormed member
  have valid : graph.vertices.idxOf port.vertex < (degrees graph).length := by
    simpa [degrees] using List.idxOf_lt_length_iff.mpr vertexMember
  have bound := block_within_total (degrees graph) valid
  rw [degree_at_index vertexMember,degrees_sum wellFormed] at bound
  rw [show (degrees graph).length = graph.vertices.length from by simp [degrees]] at bound
  have rank := port_rank_bound member
  have positive : 2 ≤ blockStart (degrees graph) (graph.vertices.idxOf port.vertex) := by
    unfold blockStart
    omega
  unfold portX
  constructor <;> omega

end LeanTrominoes.PeriodicOrthocrossing.GeneralPorts
