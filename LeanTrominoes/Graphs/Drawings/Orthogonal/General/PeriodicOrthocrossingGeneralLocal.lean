/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Orthogonal.General.PeriodicOrthocrossingGeneralLocalCore
import LeanTrominoes.Graphs.Drawings.Orthogonal.General.PeriodicOrthocrossingGeneralFanBounds

/-! # Real locality of every edge route in the general construction -/
namespace LeanTrominoes.PeriodicOrthocrossing.GeneralPorts

private theorem origin_point_in_rectangle {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} (orthogonal : Bool) (offset point : Cell)
    (bounds : 0 ≤ point.1 ∧ point.1 ≤ drawingGridSize graph ∧ 0 ≤ point.2 ∧ point.2 ≤ drawingGridSize graph) :
    (drawing graph orthogonal).PointInLocalRectangle offset point := by
  unfold PeriodicGridDrawing.PointInLocalRectangle
  rw [drawing_gridSize]
  constructor
  · exact le_trans (min_le_left _ _) bounds.1
  constructor
  · have nonnegative := le_max_left 0 ((drawingGridSize graph : Int)*offset.1)
    omega
  constructor
  · exact le_trans (min_le_left _ _) bounds.2.2.1
  · have nonnegative := le_max_left 0 ((drawingGridSize graph : Int)*offset.2)
    omega

private theorem translated_point_in_rectangle {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} (orthogonal : Bool) (offset point : Cell)
    (bounds : 0 ≤ point.1 ∧ point.1 ≤ drawingGridSize graph ∧ 0 ≤ point.2 ∧ point.2 ≤ drawingGridSize graph) :
    (drawing graph orthogonal).PointInLocalRectangle offset
      (Cell.add (Cell.scale (drawingGridSize graph : Int) offset) point) := by
  unfold PeriodicGridDrawing.PointInLocalRectangle
  rw [drawing_gridSize]
  simp only [Cell.add,Cell.scale]
  have xl := min_le_right 0 ((drawingGridSize graph : Int)*offset.1)
  have xh := le_max_right 0 ((drawingGridSize graph : Int)*offset.1)
  have yl := min_le_right 0 ((drawingGridSize graph : Int)*offset.2)
  have yh := le_max_right 0 ((drawingGridSize graph : Int)*offset.2)
  constructor <;> first | omega | constructor <;> omega

theorem route_points_in_local_rectangle {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed) (orthogonal : Bool) {tagged : PeriodicEdge Vertex × Nat}
    (member : tagged ∈ graph.edges.zipIdx) (edgeLocal : tagged.1.span ≤ 1) :
    ∀ point ∈ route graph orthogonal tagged.1 tagged.2,
      (drawing graph orthogonal).PointInLocalRectangle tagged.1.offset point := by
  have gridBound : (3 : Int) ≤ drawingGridSize graph := by unfold drawingGridSize; omega
  have source := fan_point_bounds wellFormed orthogonal (sourcePort_mem_allPorts graph member)
  have target := fan_point_bounds wellFormed orthogonal (targetPort_mem_allPorts graph member)
  intro point pointMember
  simp only [route,joinPolylines,List.mem_append] at pointMember
  rcases pointMember with (sourceMember | coreMember) | targetMember
  · have bounds := source point sourceMember
    exact origin_point_in_rectangle orthogonal tagged.1.offset point (by omega)
  · exact core_points_in_local_rectangle wellFormed orthogonal member edgeLocal point
      (List.mem_of_mem_tail coreMember)
  · have member := List.mem_of_mem_tail targetMember
    unfold translatePolyline at member
    obtain ⟨original,originalMember,rfl⟩ := List.mem_map.mp member
    have bounds := target original (List.mem_reverse.mp originalMember)
    exact translated_point_in_rectangle orthogonal tagged.1.offset original (by omega)

attribute [local irreducible] drawing route core fan

theorem drawing_isRealLocal {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed) (orthogonal : Bool) (isLocal : graph.IsLocal) :
    (drawing graph orthogonal).IsRealLocal graph := by
  intro tagged member point contains
  rw [drawing_edgeRoute_of_mem graph orthogonal member] at contains
  have edgeLocal := isLocal tagged.1 (List.fst_mem_of_mem_zipIdx member)
  exact PeriodicGridDrawing.real_local_of_rectangle edgeLocal
    (PeriodicGridDrawing.realContains_in_local_rectangle
      (route_points_in_local_rectangle wellFormed orthogonal member edgeLocal) contains)

end LeanTrominoes.PeriodicOrthocrossing.GeneralPorts
