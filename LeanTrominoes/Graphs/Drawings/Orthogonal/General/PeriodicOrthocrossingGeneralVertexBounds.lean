/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Orthogonal.General.PeriodicOrthocrossingGeneralCorePortBands
import LeanTrominoes.Graphs.Drawings.Orthogonal.General.PeriodicOrthocrossingGeneralFanBlocks

/-! # Every vertex center, including an isolated vertex, precedes all gate columns -/
namespace LeanTrominoes.PeriodicOrthocrossing.GeneralPorts

theorem indexed_vertex_bounds {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed) {index : Nat} (valid : index < graph.vertices.length) :
    1 ≤ (position graph index).1 ∧ (position graph index).1 < drawingGridSize graph ∧
      ∀ gateIndex, (position graph index).1 < gateX graph gateIndex := by
  have countValid : index < (degrees graph).length := by simpa [degrees] using valid
  have within := block_within_total (degrees graph) countValid
  rw [degrees_sum wellFormed,show (degrees graph).length = graph.vertices.length from by simp [degrees]] at within
  have positive : 2 ≤ blockStart (degrees graph) index := by unfold blockStart; omega
  simp only [position,gateX,drawingGridSize]
  constructor
  · omega
  constructor
  · omega
  intro gateIndex
  omega

theorem fan_block_finish_before_index {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed) {port : GraphPort Vertex} (member : port ∈ allPorts graph)
    {index : Nat} (ordered : graph.vertices.idxOf port.vertex < index) :
    fanBlockFinish graph port.vertex < (blockStart (degrees graph) index : Int) := by
  have vertexMember := port_vertex_mem wellFormed member
  have valid : graph.vertices.idxOf port.vertex < (degrees graph).length := by
    simpa [degrees] using List.idxOf_lt_length_iff.mpr vertexMember
  have separation := block_separated (degrees graph) valid ordered
  have degreeEq : (degrees graph)[graph.vertices.idxOf port.vertex]'valid = (portsAt graph port.vertex).length := by
    simp [degrees,List.getElem_idxOf (List.idxOf_lt_length_iff.mpr vertexMember)]
  rw [degreeEq] at separation
  unfold fanBlockFinish fanBlockStart
  omega

end LeanTrominoes.PeriodicOrthocrossing.GeneralPorts
