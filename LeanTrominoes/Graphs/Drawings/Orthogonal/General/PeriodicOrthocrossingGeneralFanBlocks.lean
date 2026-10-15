/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Orthogonal.General.PeriodicOrthocrossingGeneralFanBounds
import LeanTrominoes.Common.Geometry.GridPolylineRealBounds
import LeanTrominoes.Common.Geometry.GridPolylineRealAlgebra
import LeanTrominoes.Common.Geometry.GridSegmentRealPeriodicSeparation

/-! # Closed real fan images stay in disjoint vertex blocks -/
namespace LeanTrominoes.PeriodicOrthocrossing.GeneralPorts

def fanBlockStart {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex) (vertex : Vertex) : Int :=
  blockStart (degrees graph) (graph.vertices.idxOf vertex)

def fanBlockFinish {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex) (vertex : Vertex) : Int :=
  fanBlockStart graph vertex+(portsAt graph vertex).length+2

theorem fan_block_points {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    (orthogonal : Bool) {port : GraphPort Vertex} (member : port ∈ allPorts graph) :
    ∀ point ∈ fan graph orthogonal port,
      fanBlockStart graph port.vertex ≤ point.1 ∧ point.1 ≤ fanBlockFinish graph port.vertex ∧
        1 ≤ point.2 ∧ point.2 ≤ 3 := by
  have rank := port_rank_bound member
  cases orthogonal
  · simp [fan,fanBlockStart,fanBlockFinish,vertexX,portX]
    omega
  · have localBounds : ∀ rank : Fin 4, ∀ point ∈ degreeFourFan rank,
        -1 ≤ point.1 ∧ point.1 ≤ 2 ∧ 1 ≤ point.2 ∧ point.2 ≤ 3 := by decide +kernel
    intro point pointMember
    change point ∈ (degreeFourFan ⟨portRank graph port % 4,Nat.mod_lt _ (by decide)⟩).map
      (Cell.add (vertexX graph port.vertex,0)) at pointMember
    obtain ⟨localPoint,localMember,rfl⟩ := List.mem_map.mp pointMember
    have bounds := localBounds _ localPoint localMember
    simp only [Cell.add,vertexX,fanBlockStart,fanBlockFinish]
    omega

theorem fan_block_bounds {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed) {port : GraphPort Vertex} (member : port ∈ allPorts graph) :
    1 ≤ fanBlockStart graph port.vertex ∧ fanBlockFinish graph port.vertex < drawingGridSize graph := by
  have vertexMember := port_vertex_mem wellFormed member
  have valid : graph.vertices.idxOf port.vertex < (degrees graph).length := by
    simpa [degrees] using List.idxOf_lt_length_iff.mpr vertexMember
  have within := block_within_total (degrees graph) valid
  have degreeEq : (degrees graph)[graph.vertices.idxOf port.vertex]'valid = (portsAt graph port.vertex).length := by
    simp [degrees,List.getElem_idxOf (List.idxOf_lt_length_iff.mpr vertexMember)]
  rw [degreeEq,degrees_sum wellFormed,show (degrees graph).length = graph.vertices.length from by simp [degrees]] at within
  have positive : 2 ≤ blockStart (degrees graph) (graph.vertices.idxOf port.vertex) := by unfold blockStart; omega
  unfold fanBlockFinish fanBlockStart drawingGridSize
  omega

theorem fan_blocks_separated {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed) {first second : GraphPort Vertex}
    (firstMember : first ∈ allPorts graph)
    (ordered : graph.vertices.idxOf first.vertex < graph.vertices.idxOf second.vertex) :
    fanBlockFinish graph first.vertex < fanBlockStart graph second.vertex := by
  have vertexMember := port_vertex_mem wellFormed firstMember
  have valid : graph.vertices.idxOf first.vertex < (degrees graph).length := by
    simpa [degrees] using List.idxOf_lt_length_iff.mpr vertexMember
  have separation := block_separated (degrees graph) valid ordered
  have degreeEq : (degrees graph)[graph.vertices.idxOf first.vertex]'valid = (portsAt graph first.vertex).length := by
    simp [degrees,List.getElem_idxOf (List.idxOf_lt_length_iff.mpr vertexMember)]
  rw [degreeEq] at separation
  unfold fanBlockFinish fanBlockStart
  omega

theorem fan_block_finish_bound {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed) {port : GraphPort Vertex} (member : port ∈ allPorts graph) :
    fanBlockFinish graph port.vertex < 3*graph.vertices.length+2*graph.edges.length+2 := by
  have vertexMember := port_vertex_mem wellFormed member
  have valid : graph.vertices.idxOf port.vertex < (degrees graph).length := by
    simpa [degrees] using List.idxOf_lt_length_iff.mpr vertexMember
  have within := block_within_total (degrees graph) valid
  have degreeEq : (degrees graph)[graph.vertices.idxOf port.vertex]'valid = (portsAt graph port.vertex).length := by
    simp [degrees,List.getElem_idxOf (List.idxOf_lt_length_iff.mpr vertexMember)]
  rw [degreeEq,degrees_sum wellFormed,show (degrees graph).length = graph.vertices.length from by simp [degrees]] at within
  unfold fanBlockFinish fanBlockStart
  omega

theorem fan_real_block_bounds {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    (orthogonal : Bool) {port : GraphPort Vertex} (member : port ∈ allPorts graph) {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains (fan graph orthogonal port) point) :
    (fanBlockStart graph port.vertex : ℝ) ≤ point.1 ∧ point.1 ≤ (fanBlockFinish graph port.vertex : ℝ) ∧
      1 ≤ point.2 ∧ point.2 ≤ 3 := by
  simpa using GridPolyline.realContains_bounds (fan_block_points orthogonal member) contains

theorem fan_contacts_same_vertex {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed) (orthogonal : Bool) {first second : GraphPort Vertex}
    (firstMember : first ∈ allPorts graph) (secondMember : second ∈ allPorts graph) {point : ℝ × ℝ}
    (firstContains : GridPolyline.RealContains (fan graph orthogonal first) point)
    (secondContains : GridPolyline.RealContains (fan graph orthogonal second) point) : first.vertex = second.vertex := by
  have firstBounds := fan_real_block_bounds orthogonal firstMember firstContains
  have secondBounds := fan_real_block_bounds orthogonal secondMember secondContains
  have indices : graph.vertices.idxOf first.vertex = graph.vertices.idxOf second.vertex := by
    rcases lt_trichotomy (graph.vertices.idxOf first.vertex) (graph.vertices.idxOf second.vertex) with less | equal | greater
    · have gap := fan_blocks_separated wellFormed firstMember less
      have realGap : (fanBlockFinish graph first.vertex : ℝ) < fanBlockStart graph second.vertex := by exact_mod_cast gap
      linarith [firstBounds.2.1,secondBounds.1]
    · exact equal
    · have gap := fan_blocks_separated wellFormed secondMember greater
      have realGap : (fanBlockFinish graph second.vertex : ℝ) < fanBlockStart graph first.vertex := by exact_mod_cast gap
      linarith [secondBounds.2.1,firstBounds.1]
  exact (List.idxOf_inj (port_vertex_mem wellFormed firstMember)).mp indices

end LeanTrominoes.PeriodicOrthocrossing.GeneralPorts
