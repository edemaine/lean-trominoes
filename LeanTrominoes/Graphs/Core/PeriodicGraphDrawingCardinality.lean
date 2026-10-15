/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawing
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-! # Vertex and edge bounds for periodic grid drawings -/
namespace LeanTrominoes
open scoped BigOperators

theorem PeriodicGraph.incidences_length {Vertex : Type*} (graph : PeriodicGraph Vertex) :
    graph.incidences.length = 2*graph.edges.length := by
  unfold PeriodicGraph.incidences
  induction graph.edges with
  | nil => simp
  | cons edge rest ih => simp [PeriodicEdge.incidences,ih]; omega

theorem PeriodicGraph.edge_count_bound {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} (wellFormed : graph.IsWellFormed)
    {bound : Nat} (degree : graph.DegreeAtMost bound) :
    2*graph.edges.length ≤ bound*graph.vertices.length := by
  have support : graph.incidences.toFinset ⊆ graph.vertices.toFinset := by
    intro vertex member
    simp only [List.mem_toFinset,PeriodicGraph.incidences,List.mem_flatMap] at member
    obtain ⟨edge,edgeMember,endpoint⟩ := member
    simp only [PeriodicEdge.incidences,List.mem_cons,List.not_mem_nil,or_false] at endpoint
    simp only [List.mem_toFinset]
    rcases endpoint with rfl | rfl
    · exact (wellFormed.2 edge edgeMember).1
    · exact (wellFormed.2 edge edgeMember).2
  have sum : ∑ vertex ∈ graph.vertices.toFinset, graph.incidences.count vertex = graph.incidences.length := by
    rw [← List.sum_toFinset_count_eq_length]
    symm
    apply Finset.sum_subset support
    intro vertex _ absent
    exact List.count_eq_zero.mpr (by simpa using absent)
  calc
    2*graph.edges.length = ∑ vertex ∈ graph.vertices.toFinset, graph.incidences.count vertex :=
      (sum.trans (PeriodicGraph.incidences_length graph)).symm
    _ ≤ ∑ _vertex ∈ graph.vertices.toFinset, bound :=
      Finset.sum_le_sum (fun vertex _ => degree vertex)
    _ = bound*graph.vertices.length := by
      simp [List.toFinset_card_of_nodup wellFormed.1,Nat.mul_comm]

theorem PeriodicGridDrawing.vertex_count_bound {drawing : PeriodicGridDrawing}
    (distinct : drawing.vertexPositions.Nodup)
    (inside : ∀ point ∈ drawing.vertexPositions,
      0 < point.1 ∧ point.1 < drawing.gridSize ∧ 0 < point.2 ∧ point.2 < drawing.gridSize) :
    drawing.vertexPositions.length ≤ drawing.gridSize^2 := by
  let interval : Finset Int := Finset.Ico 0 (drawing.gridSize : Int)
  have subset : drawing.vertexPositions.toFinset ⊆ interval ×ˢ interval := by
    intro point member
    have bounds := inside point (List.mem_toFinset.mp member)
    simp only [Finset.mem_product,interval,Finset.mem_Ico]
    exact ⟨⟨bounds.1.le,bounds.2.1⟩,⟨bounds.2.2.1.le,bounds.2.2.2⟩⟩
  have cardinal := Finset.card_le_card subset
  simpa [interval,List.toFinset_card_of_nodup distinct,pow_two] using cardinal

theorem PeriodicGridDrawing.compatible_vertex_count_bound {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (compatible : drawing.IsCompatible graph) : graph.vertices.length ≤ drawing.gridSize^2 := by
  rw [← compatible.2.1]
  exact vertex_count_bound compatible.2.2.2.1 compatible.2.2.2.2.1

theorem PeriodicGridDrawing.compatible_edge_count_bound {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (compatible : drawing.IsCompatible graph) (degree : graph.DegreeAtMost 4) :
    graph.edges.length ≤ 2*drawing.gridSize^2 := by
  have handshaking := PeriodicGraph.edge_count_bound compatible.1 degree
  have vertices := compatible_vertex_count_bound compatible
  omega

/-- Nine copies of the protoedge table have at most eighteen times the
squared grid size entries. -/
theorem PeriodicGridDrawing.nine_copy_edge_count_bound {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (compatible : drawing.IsCompatible graph) (degree : graph.DegreeAtMost 4) :
    9*graph.edges.length ≤ 18*drawing.gridSize^2 := by
  have edges := compatible_edge_count_bound compatible degree
  omega

end LeanTrominoes
