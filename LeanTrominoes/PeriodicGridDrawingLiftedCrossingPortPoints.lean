/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRectangleRowPortJoins
import LeanTrominoes.PeriodicGridDrawingPaddedCrossingRoutes

/-! # Crossing-bar endpoints match rectangle ports in every period, including column zero -/
namespace LeanTrominoes.PeriodicGridDrawing
open PeriodicOrthocrossing OrthogonalDrawingRefinement

theorem rectangleLiftedPortPoint_eq_translate {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) (column : Nat) (cell : Cell) (key : RectanglePortKey Vertex) :
    rectangleLiftedPortPoint graph drawing column cell key =
      Cell.add (Cell.scale (paddedGridSize drawing.gridSize) cell) (rectangleIntegralPortPoint graph drawing column key) := by
  unfold rectangleLiftedPortPoint
  rw [rectangleRouteOffset_eq_translate]
  apply Prod.ext <;> simp [rectangleIntegralPortPoint,Cell.add] <;> ring

theorem paddedCrossingRoute_boundary_port {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) (column : Nat) (right : Bool) (key : Nat × Cell) :
    (if right then (paddedCrossingRoute graph drawing ((column+if right then 1 else 0 : Nat) : Int) key).head?
      else (paddedCrossingRoute graph drawing ((column+if right then 1 else 0 : Nat) : Int) key).getLast?) =
      some (rectangleIntegralPortPoint graph drawing column (.vertical right (.crossing key))) := by
  cases right
  · rw [rectangle_crossing_port_point]
    simp [paddedCrossingRoute,enlargedCrossingBar]
  · exact paddedCrossingRoute_head_joins_rectangle graph drawing column key

theorem paddedCrossingRoute_lifted_boundary_port {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) (index column : Nat) (cell : Cell) (right : Bool) :
    (if right then (paddedCrossingRoute graph drawing
        (((column+if right then 1 else 0 : Nat) : Int)+(drawing.gridSize : Int)*cell.1) (index,(0,0))).head?
      else (paddedCrossingRoute graph drawing
        (((column+if right then 1 else 0 : Nat) : Int)+(drawing.gridSize : Int)*cell.1) (index,(0,0))).getLast?) =
      some (rectangleLiftedPortPoint graph drawing column cell (.vertical right (.crossing (index,Cell.scale (-1) cell)))) := by
  have keyZero : Cell.add (Cell.scale (-1) cell) cell = (0,0) := by apply Prod.ext <;> simp [Cell.add,Cell.scale]
  have translation := paddedCrossingRoute_add_cell graph drawing ((column+if right then 1 else 0 : Nat) : Int)
    (index,Cell.scale (-1) cell) cell
  rw [keyZero] at translation
  rw [rectangleLiftedPortPoint_eq_translate]
  have port := paddedCrossingRoute_boundary_port graph drawing column right (index,Cell.scale (-1) cell)
  cases right
  · simp only [Bool.false_eq_true,if_false,add_zero] at translation port ⊢
    rw [translation]
    simp only [translatePolyline,List.getLast?_map,port,Option.map_some]
  · simp only [if_true] at translation port ⊢
    rw [translation]
    simp only [translatePolyline,List.head?_map,port,Option.map_some]

end LeanTrominoes.PeriodicGridDrawing
