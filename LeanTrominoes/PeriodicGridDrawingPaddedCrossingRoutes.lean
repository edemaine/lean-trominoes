/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRectanglePortJoins
import LeanTrominoes.OrthogonalEnlargedCrossingBarSeparation

/-! # Actual crossing routes join the neighboring rectangle ports periodically -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement PeriodicOrthocrossing

def paddedCrossingRoute {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (line : Int) (key : Nat × Cell) : List Cell :=
  enlargedCrossingBar (paddedRefinementFactor drawing.gridSize) (crossingBound drawing.gridSize) line
    (paddedPeriodicColumnHeight graph drawing line ((drawing.liftedStraightSegment key.1 key.2).rationalLineHeight line))

theorem paddedCrossingRoute_isRealOpenSimple {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (line : Int) (key : Nat × Cell) : GridPolyline.IsRealOpenSimple (paddedCrossingRoute graph drawing line key) := by
  apply enlargedCrossingBar_isRealOpenSimple
  have positive : 0 < drawing.gridSize := Nat.zero_lt_succ drawing.gridSizePred
  unfold crossingBound
  positivity

theorem paddedCrossingRoute_orthogonal {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (line : Int) (key : Nat × Cell) : OrthogonalPolyline (paddedCrossingRoute graph drawing line key) := by
  apply enlargedCrossingBar_orthogonal
  have positive : 0 < drawing.gridSize := Nat.zero_lt_succ drawing.gridSizePred
  unfold crossingBound
  positivity

theorem paddedCrossingRoute_head_joins_rectangle {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) (column : Nat) (key : Nat × Cell) :
    (paddedCrossingRoute graph drawing (column+1) key).head? =
      some (rectangleIntegralPortPoint graph drawing column (.vertical true (.crossing key))) := by
  rw [rectangle_crossing_port_point]
  simp [paddedCrossingRoute,enlargedCrossingBar,sub_eq_add_neg]

theorem paddedCrossingRoute_last_joins_rectangle {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) (column : Nat) (key : Nat × Cell) :
    (paddedCrossingRoute graph drawing (column+1) key).getLast? =
      some (rectangleIntegralPortPoint graph drawing (column+1) (.vertical false (.crossing key))) := by
  rw [rectangle_crossing_port_point]
  simp [paddedCrossingRoute,enlargedCrossingBar]

theorem paddedCrossingHeight_add_cell {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (line : Int) (key : Nat × Cell) (shift : Cell) :
    paddedPeriodicColumnHeight graph drawing (line+(drawing.gridSize : Int)*shift.1)
      ((drawing.liftedStraightSegment key.1 (Cell.add key.2 shift)).rationalLineHeight (line+(drawing.gridSize : Int)*shift.1)) =
      paddedPeriodicColumnHeight graph drawing line ((drawing.liftedStraightSegment key.1 key.2).rationalLineHeight line)+
        (paddedGridSize drawing.gridSize : Int)*shift.2 := by
  rw [liftedStraightSegment_add_cell]
  have height := GridSegment.rationalLineHeight_translate (drawing.liftedStraightSegment key.1 key.2) (drawing.periodTranslation shift) line
  simp only [periodTranslation,Cell.scale,Int.cast_mul,Int.cast_natCast] at height
  simp only [periodTranslation,Cell.scale]
  rw [height,paddedPeriodicColumnHeight_translate]

theorem paddedCrossingRoute_add_cell {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (line : Int) (key : Nat × Cell) (shift : Cell) :
    paddedCrossingRoute graph drawing (line+(drawing.gridSize : Int)*shift.1) (key.1,Cell.add key.2 shift) =
      translatePolyline (Cell.scale (paddedGridSize drawing.gridSize) shift) (paddedCrossingRoute graph drawing line key) := by
  unfold paddedCrossingRoute
  dsimp only [Prod.fst,Prod.snd]
  rw [paddedCrossingHeight_add_cell graph drawing line key shift]
  simp only [enlargedCrossingBar,translatePolyline,List.map_cons,List.map_nil]
  apply congrArg₂ List.cons
  · apply Prod.ext <;> simp [Cell.add,Cell.scale,paddedGridSize] <;> ring
  · apply congrArg (fun point : Cell => [point])
    apply Prod.ext <;> simp [Cell.add,Cell.scale,paddedGridSize] <;> ring

end LeanTrominoes.PeriodicGridDrawing
