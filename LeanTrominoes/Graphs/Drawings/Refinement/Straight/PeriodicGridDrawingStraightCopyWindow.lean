/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Common.Geometry.GridSegmentRealLocalCopyWindow
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingVertexCoverage
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingRealGeometry
import LeanTrominoes.Graphs.Drawings.Orthogonal.Crossings.PeriodicOrthocrossingCrossings

/-! # The nine-copy window exhausts straight local edges in a compatible drawing -/
namespace LeanTrominoes.PeriodicGridDrawing
open PeriodicOrthocrossing

theorem straight_realEdgeRoute_copy_window {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible graph)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (straight : (drawing.edgeRoute tagged.2).length = 2) (edgeLocal : tagged.1.span ≤ 1)
    (cell : Cell) {point : ℝ × ℝ}
    (inside : 0 ≤ point.1 ∧ point.1 ≤ (drawing.gridSize : ℝ) ∧ 0 ≤ point.2 ∧ point.2 ≤ (drawing.gridSize : ℝ))
    (contains : GridPolyline.RealContains (drawing.realEdgeRoute tagged.2 cell) point) : cell ∈ neighborTranslations := by
  have ends := compatible.2.2.2.2.2 tagged member
  obtain ⟨first,second,routeEq⟩ := List.length_eq_two.mp straight
  have firstEq : first = drawing.vertexPosition graph tagged.1.source := by simpa [routeEq] using ends.1
  have secondEq : second = Cell.add (drawing.vertexPosition graph tagged.1.target) (drawing.periodTranslation tagged.1.offset) := by
    simpa [routeEq] using ends.2
  rw [PeriodicGridDrawing.realEdgeRoute,routeEq] at contains
  obtain ⟨segment,segmentMember,segmentContains⟩ := contains
  simp only [List.map_cons,List.map_nil,gridPolylineSegments,List.mem_cons,List.not_mem_nil,or_false] at segmentMember
  subst segment
  rw [firstEq,secondEq] at segmentContains
  have actual : GridSegment.RealContains
      ⟨Cell.add (drawing.vertexPosition graph tagged.1.source) (Cell.scale drawing.gridSize cell),
        Cell.add (drawing.vertexPosition graph tagged.1.target) (Cell.scale drawing.gridSize (Cell.add cell tagged.1.offset))⟩ point := by
    convert segmentContains using 1 <;> congr 1
    all_goals apply Prod.ext <;> simp [periodTranslation,Cell.add,Cell.scale] <;> ring
  have endpoints := compatible.1.2 tagged.1 (List.fst_mem_of_mem_zipIdx member)
  have sourceBounds := compatible.2.2.2.2.1 _ (compatible.vertexPosition_mem endpoints.1)
  have targetBounds := compatible.2.2.2.2.1 _ (compatible.vertexPosition_mem endpoints.2)
  have positive : (0 : Int) < drawing.gridSize := by exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
  have offsetBounds : -1 ≤ tagged.1.offset.1 ∧ tagged.1.offset.1 ≤ 1 ∧
      -1 ≤ tagged.1.offset.2 ∧ tagged.1.offset.2 ≤ 1 := by
    unfold PeriodicEdge.span at edgeLocal
    omega
  have window := GridSegment.real_local_segment_copy_window positive sourceBounds targetBounds offsetBounds inside actual
  apply (mem_neighborTranslations_iff cell).mpr
  exact ⟨by omega,by omega⟩

end LeanTrominoes.PeriodicGridDrawing
