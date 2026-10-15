/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingLiftedCrossingPortPoints
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingPaddedIncidenceIsolation
import LeanTrominoes.Common.Geometry.GridPolylineRealEndpointContainment

/-! # Every lifted vertical rectangle port lies on its own crossing bar or fan -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement PeriodicOrthocrossing GeneralVertexNormalization

theorem rectangle_crossing_port_on_bar {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) (column : Nat) (cell : Cell)
    (right : Bool) (key : Nat × Cell) :
    GridPolyline.RealContains (paddedCrossingRoute graph drawing
      (((column+if right then 1 else 0 : Nat) : Int)+(drawing.gridSize : Int)*cell.1)
      (key.1,Cell.add key.2 cell))
      (realCell (rectangleLiftedPortPoint graph drawing column cell (.vertical right (.crossing key)))) := by
  have endpoint := paddedCrossingRoute_boundary_port graph drawing column right key
  rw [paddedCrossingRoute_add_cell,rectangleLiftedPortPoint_eq_translate]
  have contains : GridPolyline.RealContains
      (paddedCrossingRoute graph drawing ((column+if right then 1 else 0 : Nat) : Int) key)
      (realCell (rectangleIntegralPortPoint graph drawing column (.vertical right (.crossing key)))) := by
    have long := (paddedCrossingRoute_isRealOpenSimple graph drawing ((column+if right then 1 else 0 : Nat) : Int) key).1
    cases right
    · exact GridPolyline.realContains_last long endpoint
    · exact GridPolyline.realContains_head long endpoint
  have translated := (GridPolyline.realContains_translate (Cell.scale (paddedGridSize drawing.gridSize) cell) _ _).mpr contains
  simpa only [realCell,Cell.add,Int.cast_add] using translated

theorem rectangle_incidence_port_on_fan {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (column : Nat) (cell : Cell) (right : Bool) {tagged : PeriodicEdge Vertex × Nat} {target : Bool}
    (valid : (RectanglePortKey.vertical right (.incidence tagged target)).Valid graph drawing column) :
    GridPolyline.RealContains (liftedPaddedIncidenceRoute graph drawing (endpointPort tagged target) cell)
      (realCell (rectangleLiftedPortPoint graph drawing column cell (.vertical right (.incidence tagged target)))) := by
  have last := rectangle_incidence_port_is_fan_endpoint planar degree straight column right valid
  have contains := GridPolyline.realContains_last (paddedIncidenceRoute_isRealOpenSimple graph drawing (endpointPort tagged target)).1 last
  rw [liftedPaddedIncidenceRoute_eq_translate,rectangleLiftedPortPoint_eq_translate]
  have translated := (GridPolyline.realContains_translate (Cell.scale (paddedGridSize drawing.gridSize) cell) _ _).mpr contains
  simpa only [realCell,Cell.add,Int.cast_add] using translated

theorem rectangle_crossing_port_lifted_crosses {Vertex : Type*}
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (column : Nat) (cell : Cell) (right : Bool)
    {key : Nat × Cell} (valid : (RectanglePortKey.vertical right (.crossing key)).Valid graph drawing column) :
    (drawing.liftedStraightSegment key.1 (Cell.add key.2 cell)).CrossesVerticalLine
      (((column+if right then 1 else 0 : Nat) : Int)+(drawing.gridSize : Int)*cell.1) := by
  have crosses := (of_decide_eq_true (List.mem_filter.mp valid).2).1
  rw [liftedStraightSegment_add_cell]
  simpa only [periodTranslation,Cell.scale] using
    (GridSegment.crossesVerticalLine_translate (drawing.liftedStraightSegment key.1 key.2)
      (drawing.periodTranslation cell) ((column+if right then 1 else 0 : Nat) : Int)).mpr crosses

end LeanTrominoes.PeriodicGridDrawing
