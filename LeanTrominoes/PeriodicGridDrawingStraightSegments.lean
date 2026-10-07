/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GridPolylineRealAlgebra

/-! # Straight routes and their lifted segment representation -/
namespace LeanTrominoes.PeriodicGridDrawing
open PeriodicOrthocrossing

def straightSegment (drawing : PeriodicGridDrawing) (index : Nat) : GridSegment :=
  ⟨(drawing.edgeRoute index).head?.getD (0,0),(drawing.edgeRoute index).getLast?.getD (0,0)⟩

def liftedStraightSegment (drawing : PeriodicGridDrawing) (index : Nat) (cell : Cell) : GridSegment :=
  (drawing.straightSegment index).translate (drawing.periodTranslation cell)

theorem realEdgeRoute_straight_image (drawing : PeriodicGridDrawing) (index : Nat) (cell : Cell)
    (straight : (drawing.edgeRoute index).length = 2) (point : ℝ × ℝ) :
    GridPolyline.RealContains (drawing.realEdgeRoute index cell) point ↔
      (drawing.liftedStraightSegment index cell).RealContains point := by
  obtain ⟨first,second,routeEq⟩ := List.length_eq_two.mp straight
  simp [GridPolyline.RealContains,realEdgeRoute,routeEq,gridPolylineSegments,
    liftedStraightSegment,straightSegment,GridSegment.translate]

theorem realEdgeRoute_straight_endpoints (drawing : PeriodicGridDrawing) (index : Nat) (cell : Cell)
    (straight : (drawing.edgeRoute index).length = 2) (point : ℝ × ℝ) :
    GridPolyline.RealIsEndpoint (drawing.realEdgeRoute index cell) point ↔
      point = realCell (drawing.liftedStraightSegment index cell).start ∨
        point = realCell (drawing.liftedStraightSegment index cell).finish := by
  obtain ⟨first,second,routeEq⟩ := List.length_eq_two.mp straight
  simp [GridPolyline.RealIsEndpoint,realEdgeRoute,routeEq,liftedStraightSegment,straightSegment,GridSegment.translate]

end LeanTrominoes.PeriodicGridDrawing
