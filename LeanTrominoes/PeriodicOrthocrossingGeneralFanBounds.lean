/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicOrthocrossingGeneralOrthogonal

/-! # The complete vertex fans stay inside the fundamental cell -/
namespace LeanTrominoes.PeriodicOrthocrossing.GeneralPorts

theorem vertexX_bounds {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed) {vertex : Vertex} (member : vertex ∈ graph.vertices) :
    1 ≤ vertexX graph vertex ∧ vertexX graph vertex+2 < drawingGridSize graph := by
  have valid : graph.vertices.idxOf vertex < (degrees graph).length := by
    simpa [degrees] using List.idxOf_lt_length_iff.mpr member
  have bound := block_within_total (degrees graph) valid
  rw [degrees_sum wellFormed,show (degrees graph).length = graph.vertices.length from by simp [degrees]] at bound
  have positive : 2 ≤ blockStart (degrees graph) (graph.vertices.idxOf vertex) := by unfold blockStart; omega
  unfold vertexX drawingGridSize
  constructor <;> omega

private theorem degreeFourFan_point_bounds (rank : Fin 4) :
    ∀ point ∈ degreeFourFan rank, -1 ≤ point.1 ∧ point.1 ≤ 2 ∧ 1 ≤ point.2 ∧ point.2 ≤ 3 := by
  fin_cases rank <;> decide +kernel

theorem fan_point_bounds {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed) (orthogonal : Bool) {port : GraphPort Vertex}
    (member : port ∈ allPorts graph) :
    ∀ point ∈ fan graph orthogonal port,
      0 ≤ point.1 ∧ point.1 ≤ drawingGridSize graph ∧ 1 ≤ point.2 ∧ point.2 ≤ 3 := by
  have center := vertexX_bounds wellFormed (port_vertex_mem wellFormed member)
  have column := portX_lt_gridSize wellFormed member
  have gridPositive : (0 : Int) < drawingGridSize graph := by exact_mod_cast drawingGridSize_pos graph
  cases orthogonal
  · simp [fan]
    omega
  · intro point pointMember
    change point ∈ (degreeFourFan ⟨portRank graph port % 4,Nat.mod_lt _ (by decide)⟩).map
      (Cell.add (vertexX graph port.vertex,0)) at pointMember
    obtain ⟨localPoint,localMember,rfl⟩ := List.mem_map.mp pointMember
    have localBounds := degreeFourFan_point_bounds _ localPoint localMember
    simp only [Cell.add]
    omega

end LeanTrominoes.PeriodicOrthocrossing.GeneralPorts
