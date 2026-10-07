/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicOrthocrossingGeneralConstruction

/-! # Endpoint and vertex validity of the general track drawing -/
namespace LeanTrominoes.PeriodicOrthocrossing.GeneralPorts

theorem position_injective {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex) :
    Function.Injective (position graph) := by
  intro first second equal
  have same := congrArg Prod.fst equal
  simp only [position] at same
  rcases lt_trichotomy first second with less | equal | greater
  · have prefixBound := List.monotone_sum_take (degrees graph) less.le
    dsimp only at prefixBound
    unfold blockStart at same
    omega
  · exact equal
  · have prefixBound := List.monotone_sum_take (degrees graph) greater.le
    dsimp only at prefixBound
    unfold blockStart at same
    omega

theorem drawing_vertexPositions_nodup {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (orthogonal : Bool) : (drawing graph orthogonal).vertexPositions.Nodup := by
  have nodup := (List.nodup_zipIdx_map_snd graph.vertices).map (position_injective graph)
  rw [List.map_map] at nodup
  exact nodup

theorem drawing_vertexPosition_of_mem {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (orthogonal : Bool) {vertex : Vertex}
    (member : vertex ∈ graph.vertices) :
    (drawing graph orthogonal).vertexPosition graph vertex = position graph (graph.vertices.idxOf vertex) := by
  have valid := List.idxOf_lt_length_iff.mpr member
  have tagged : (vertex,graph.vertices.idxOf vertex) ∈ graph.vertices.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?,List.getElem?_eq_some_iff]
    exact ⟨valid,List.idxOf_get valid⟩
  unfold PeriodicGridDrawing.vertexPosition drawing
  exact getD_map_zipIdx_of_mem graph.vertices (fun tagged => position graph tagged.2) (0,0) tagged

theorem drawing_positions_in_fundamental_square {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} (wellFormed : graph.IsWellFormed) (orthogonal : Bool) :
    ∀ point ∈ (drawing graph orthogonal).vertexPositions,
      (drawing graph orthogonal).PositionInFundamentalSquare point := by
  intro point member
  change point ∈ graph.vertices.zipIdx.map (fun tagged => position graph tagged.2) at member
  obtain ⟨tagged,taggedMember,rfl⟩ := List.mem_map.mp member
  have indexValid : tagged.2 < (degrees graph).length := by
    simpa [degrees] using List.snd_lt_of_mem_zipIdx taggedMember
  have bound := block_within_total (degrees graph) indexValid
  rw [degrees_sum wellFormed,show (degrees graph).length = graph.vertices.length from by simp [degrees]] at bound
  have positive : 2 ≤ blockStart (degrees graph) tagged.2 := by unfold blockStart; omega
  unfold PeriodicGridDrawing.PositionInFundamentalSquare
  rw [drawing_gridSize]
  simp only [position,drawingGridSize]
  norm_num
  omega

theorem drawing_edgeRoute_of_mem {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (orthogonal : Bool) {tagged : PeriodicEdge Vertex × Nat}
    (member : tagged ∈ graph.edges.zipIdx) :
    (drawing graph orthogonal).edgeRoute tagged.2 = route graph orthogonal tagged.1 tagged.2 := by
  unfold PeriodicGridDrawing.edgeRoute drawing
  exact getD_map_zipIdx_of_mem graph.edges (fun tagged => route graph orthogonal tagged.1 tagged.2) [] member

theorem drawing_routesMatch {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} (wellFormed : graph.IsWellFormed) (orthogonal : Bool) :
    (drawing graph orthogonal).RoutesMatch graph := by
  intro tagged member
  have endpoints := wellFormed.2 tagged.1 (List.fst_mem_of_mem_zipIdx member)
  rw [drawing_edgeRoute_of_mem graph orthogonal member,route_head,route_last,
    drawing_vertexPosition_of_mem graph orthogonal endpoints.1,
    drawing_vertexPosition_of_mem graph orthogonal endpoints.2]
  constructor
  · rfl
  · rw [PeriodicGridDrawing.periodTranslation,drawing_gridSize]
    simp [position,vertexX,Cell.add,add_comm]

theorem drawing_isCompatible {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} (wellFormed : graph.IsWellFormed) (orthogonal : Bool) :
    (drawing graph orthogonal).IsCompatible graph := by
  refine ⟨wellFormed,?_,?_,drawing_vertexPositions_nodup graph orthogonal,
    drawing_positions_in_fundamental_square wellFormed orthogonal,drawing_routesMatch wellFormed orthogonal⟩
  · simp [drawing]
  · simp [drawing]

end LeanTrominoes.PeriodicOrthocrossing.GeneralPorts
