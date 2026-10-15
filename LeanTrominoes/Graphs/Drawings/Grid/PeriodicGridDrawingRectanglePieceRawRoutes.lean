/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingEdgePieceEnumeration
import LeanTrominoes.Common.Geometry.GridPolylineRealEndpointReverse

/-! # Computed rectangle pieces are their matching routes in the chosen direction -/
namespace LeanTrominoes.PeriodicGridDrawing
open PeriodicOrthocrossing

theorem rectangleEdgePiece?_raw_route {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (index column : Nat) (cell : Cell) {piece : EdgeRoutePiece}
    (lookup : rectangleEdgePiece? graph drawing index column cell = some piece)
    {first last : RectanglePortKey Vertex}
    (chord : rectangleParentChord graph drawing column (index,Cell.scale (-1) cell) = some (first,last)) :
    piece.route = if rectangleParentForward graph drawing column (index,Cell.scale (-1) cell) first last then
      liftedRectangleInputRoute graph drawing column cell (first.integralPort graph drawing column,last.integralPort graph drawing column)
    else (liftedRectangleInputRoute graph drawing column cell (first.integralPort graph drawing column,last.integralPort graph drawing column)).reverse := by
  unfold rectangleEdgePiece? at lookup
  have pieceEq := Option.some.inj (by simpa only [chord,Option.map_some] using lookup)
  subst piece
  simp only [orientedRectangleInputRoute]
  split_ifs
  · rfl
  · simp [liftedRectangleInputRoute,translatePolyline]

theorem rectangleEdgePiece?_raw_image_endpoints {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (index column : Nat) (cell : Cell) {piece : EdgeRoutePiece}
    (lookup : rectangleEdgePiece? graph drawing index column cell = some piece)
    {first last : RectanglePortKey Vertex}
    (chord : rectangleParentChord graph drawing column (index,Cell.scale (-1) cell) = some (first,last)) (point : ℝ × ℝ) :
    (GridPolyline.RealContains piece.route point ↔ GridPolyline.RealContains
      (liftedRectangleInputRoute graph drawing column cell (first.integralPort graph drawing column,last.integralPort graph drawing column)) point) ∧
    (GridPolyline.RealIsEndpoint piece.route point ↔ GridPolyline.RealIsEndpoint
      (liftedRectangleInputRoute graph drawing column cell (first.integralPort graph drawing column,last.integralPort graph drawing column)) point) := by
  rw [rectangleEdgePiece?_raw_route index column cell lookup chord]
  split_ifs
  · exact ⟨Iff.rfl,Iff.rfl⟩
  · exact ⟨GridPolyline.realContains_reverse _ _,GridPolyline.realIsEndpoint_reverse _ _⟩

end LeanTrominoes.PeriodicGridDrawing
