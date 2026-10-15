/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Orthogonal.General.PeriodicOrthocrossingGeneralOrthogonal
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingRealLocalBounds

/-! # Track cores stay within their two endpoint cells -/
namespace LeanTrominoes.PeriodicOrthocrossing.GeneralPorts

theorem core_points_in_local_rectangle {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed) (orthogonal : Bool) {tagged : PeriodicEdge Vertex × Nat}
    (member : tagged ∈ graph.edges.zipIdx) (edgeLocal : tagged.1.span ≤ 1) :
    ∀ point ∈ core graph tagged.1 tagged.2,
      (drawing graph orthogonal).PointInLocalRectangle tagged.1.offset point := by
  have sourceBounds := portX_lt_gridSize wellFormed (sourcePort_mem_allPorts graph member)
  have targetBounds := portX_lt_gridSize wellFormed (targetPort_mem_allPorts graph member)
  have tracks := edgeTrack_bounds graph member
  have indexBound : tagged.2 < graph.edges.length := List.snd_lt_of_mem_zipIdx member
  have positive : (0 : Int) < drawingGridSize graph := by exact_mod_cast drawingGridSize_pos graph
  have gatePositive : (0 : Int) < 3*graph.vertices.length+2*graph.edges.length+4+2*tagged.2 := by omega
  have gateBound : (3*graph.vertices.length+2*graph.edges.length+4+2*tagged.2 : Int) < drawingGridSize graph := by
    unfold drawingGridSize
    omega
  rcases offset_eq_of_span_le_one tagged.1 edgeLocal with offset | offset | offset | offset | offset
  · simp [core,offset,PeriodicGridDrawing.PointInLocalRectangle,drawing_gridSize,Cell.add,Cell.scale,positive.le]
    omega
  · by_cases order : portX graph (targetPort tagged.1 tagged.2) < portX graph (sourcePort tagged.1 tagged.2)
    all_goals simp [core,offset,order,PeriodicGridDrawing.PointInLocalRectangle,drawing_gridSize,
      Cell.add,Cell.scale,positive.le]; omega
  · by_cases order : portX graph (sourcePort tagged.1 tagged.2) < portX graph (targetPort tagged.1 tagged.2)
    all_goals simp [core,offset,order,PeriodicGridDrawing.PointInLocalRectangle,drawing_gridSize,
      Cell.add,Cell.scale,positive.le]; omega
  · simp [core,offset,PeriodicGridDrawing.PointInLocalRectangle,drawing_gridSize,Cell.add,Cell.scale,positive.le]
    omega
  · simp [core,offset,PeriodicGridDrawing.PointInLocalRectangle,drawing_gridSize,Cell.add,Cell.scale,positive.le]
    omega

theorem core_real_local {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed) (orthogonal : Bool) {tagged : PeriodicEdge Vertex × Nat}
    (member : tagged ∈ graph.edges.zipIdx) (edgeLocal : tagged.1.span ≤ 1) {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains (core graph tagged.1 tagged.2) point) :
    (drawing graph orthogonal).RealPointInCell (0,0) point ∨
      (drawing graph orthogonal).RealPointInCell tagged.1.offset point := by
  exact PeriodicGridDrawing.real_local_of_rectangle edgeLocal
    (PeriodicGridDrawing.realContains_in_local_rectangle
      (core_points_in_local_rectangle wellFormed orthogonal member edgeLocal) contains)

end LeanTrominoes.PeriodicOrthocrossing.GeneralPorts
