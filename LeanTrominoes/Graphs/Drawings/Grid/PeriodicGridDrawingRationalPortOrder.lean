/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingRectanglePortTransport

/-! # Rectangle ports have a computable rational boundary order -/
namespace LeanTrominoes.PeriodicGridDrawing

def ColumnPortKey.rationalCoordinate {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (column : Int) (right : Bool) : ColumnPortKey Vertex → ℚ
  | .crossing key => perturbedColumnHeight graph drawing column key right+seamPerturbation graph drawing
  | .incidence tagged target => perturbedIncidenceHeight graph drawing tagged target right+seamPerturbation graph drawing

def RectanglePortKey.rationalCoordinate {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (column : Nat) : RectanglePortKey Vertex → ℚ
  | .vertical right key => key.rationalCoordinate graph drawing ((column+if right then 1 else 0 : Nat) : Int) right
  | .horizontal _ key => shiftedSeamAbscissa graph drawing key-seamAssignedSlab graph drawing key-columnPerturbation graph drawing

def RectanglePortKey.rationalCode {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (column : Nat) (key : RectanglePortKey Vertex) : Nat ×ₗ ℚ :=
  toLex (key.side.val,if key.side.val < 2 then key.rationalCoordinate graph drawing column else -key.rationalCoordinate graph drawing column)

theorem rectanglePort_virtual_coordinate {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (column : Nat) (key : RectanglePortKey Vertex) :
    (key.virtualPort graph drawing column).coordinate = (key.rationalCoordinate graph drawing column : ℝ) := by
  cases key with
  | vertical right key =>
    cases key <;> simp [RectanglePortKey.virtualPort,ColumnPortKey.virtualPort,RectanglePortKey.rationalCoordinate,
      ColumnPortKey.rationalCoordinate,virtualVerticalPort,virtualIncidencePort,Rat.cast_add]
  | horizontal top key =>
    simp [RectanglePortKey.virtualPort,RectanglePortKey.rationalCoordinate,virtualHorizontalPort,Rat.cast_sub,Rat.cast_intCast]

theorem rectanglePort_virtual_before_iff {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (column : Nat) (first second : RectanglePortKey Vertex) :
    (first.virtualPort graph drawing column).Before (second.virtualPort graph drawing column) ↔
      first.rationalCode graph drawing column < second.rationalCode graph drawing column := by
  simp only [RealRectangleBoundary.Port.Before,RealRectangleBoundary.Port.clockwiseCode,
    rectanglePort_virtual_side,rectanglePort_virtual_coordinate,RectanglePortKey.rationalCode,Prod.Lex.toLex_lt_toLex]
  split_ifs <;> norm_cast

end LeanTrominoes.PeriodicGridDrawing
