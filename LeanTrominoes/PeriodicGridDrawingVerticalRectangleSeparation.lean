/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingVerticalEdgeRoute
import LeanTrominoes.PeriodicGridDrawingRectangleExternalContacts

/-! # Directly scaled vertical segments avoid all rectangle routes -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement OrthogonalBoundaryRouting

theorem verticalEdgeRoute_contains_x {drawing : PeriodicGridDrawing} {index : Nat}
    (straight : (drawing.edgeRoute index).length = 2)
    (vertical : (drawing.liftedStraightSegment index (0,0)).start.1 =
      (drawing.liftedStraightSegment index (0,0)).finish.1)
    {point : ℝ × ℝ} (contains : GridPolyline.RealContains (verticalEdgeRoute drawing index) point) :
    point.1 = (paddedRefinementFactor drawing.gridSize : ℝ)*(drawing.straightSegment index).start.1 := by
  obtain ⟨first,last,routeEq⟩ := List.length_eq_two.mp straight
  have sameX : first.1 = last.1 := by
    simpa [liftedStraightSegment,straightSegment,routeEq,GridSegment.translate,Cell.add] using vertical
  have segmentContains : (GridSegment.mk (Cell.scale (paddedRefinementFactor drawing.gridSize) first)
      (Cell.scale (paddedRefinementFactor drawing.gridSize) last)).RealContains point := by
    simpa [verticalEdgeRoute,routeEq,scalePolyline,GridPolyline.RealContains,gridPolylineSegments] using contains
  rcases segmentContains with ⟨t,_,_,x,_⟩
  simp only [Cell.scale,Int.cast_mul,Int.cast_natCast] at x
  rw [← sameX] at x
  simpa [straightSegment,routeEq] using x

theorem liftedRectangleInputRoute_avoids_scaled_column {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {column : Nat} {chord : Chord} (member : chord ∈ rectangleChordFamily graph drawing column)
    (cell : Cell) (line : Int) {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains (liftedRectangleInputRoute graph drawing column cell chord) point)
    (atColumn : point.1 = (paddedRefinementFactor drawing.gridSize : ℝ)*line) : False := by
  have boundary := liftedRectangleInputRoute_column_strip_contact_strip_boundary planar degree graphLocal straight
    member cell contains line (by rw [atColumn]; simp)
  have positive : (0 : ℝ) < crossingBound drawing.gridSize := by exact_mod_cast crossingBound_positive drawing
  rw [atColumn,sub_self] at boundary
  rcases boundary with left | right <;> linarith

theorem verticalEdgeRoute_avoids_rectangle {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (edgeMember : tagged ∈ graph.edges.zipIdx)
    (vertical : (drawing.liftedStraightSegment tagged.2 (0,0)).start.1 =
      (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1)
    {column : Nat} {chord : Chord} (chordMember : chord ∈ rectangleChordFamily graph drawing column)
    (cell : Cell) {point : ℝ × ℝ}
    (verticalContains : GridPolyline.RealContains (verticalEdgeRoute drawing tagged.2) point)
    (rectangleContains : GridPolyline.RealContains (liftedRectangleInputRoute graph drawing column cell chord) point) : False :=
  liftedRectangleInputRoute_avoids_scaled_column planar degree graphLocal straight chordMember cell
    (drawing.straightSegment tagged.2).start.1 rectangleContains
    (verticalEdgeRoute_contains_x (straight _ edgeMember) vertical verticalContains)

end LeanTrominoes.PeriodicGridDrawing
