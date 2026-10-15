/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingRectangleInputRoutes
import LeanTrominoes.Common.Geometry.GridPolylineRealAffineSimplicity
import LeanTrominoes.Graphs.Drawings.Grid.OrthogonalBoundarySlabSeparation

/-! # Placing the computed rectangle routes in every periodic cell -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement OrthogonalBoundaryRouting PeriodicOrthocrossing

def rectangleRouteIndex (drawing : PeriodicGridDrawing) (column : Nat) (cell : Cell) : Cell :=
  ((column : Int)+(drawing.gridSize : Int)*cell.1,cell.2)

def rectangleRouteOffset (drawing : PeriodicGridDrawing) (column : Nat) (cell : Cell) : Cell :=
  drawing.paddedSlabOrigin (drawing.rectangleRouteIndex column cell).1 (drawing.rectangleRouteIndex column cell).2

def liftedRectangleInputRoute {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (column : Nat) (cell : Cell) (chord : Chord) : List Cell :=
  translatePolyline (drawing.rectangleRouteOffset column cell) (rectangleInputRoute graph drawing column chord)

theorem rectangleRouteOffset_eq_translate (drawing : PeriodicGridDrawing) (column : Nat) (cell : Cell) :
    drawing.rectangleRouteOffset column cell = Cell.add (drawing.paddedSlabOrigin column 0) (Cell.scale (paddedGridSize drawing.gridSize) cell) := by
  apply Prod.ext <;> simp [rectangleRouteOffset,rectangleRouteIndex,paddedSlabOrigin,paddedGridSize,Cell.add,Cell.scale] <;> ring

theorem rectangleRouteOffset_eq_slabOffset (drawing : PeriodicGridDrawing) (column : Nat) (cell : Cell) :
    drawing.rectangleRouteOffset column cell = slabOffset (paddedRefinementFactor drawing.gridSize) (paddedGridSize drawing.gridSize)
      (5*crossingBound drawing.gridSize) (drawing.rectangleRouteIndex column cell) := rfl

theorem liftedRectangleInputRoute_head {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (column : Nat) (cell : Cell) (chord : Chord) :
    (liftedRectangleInputRoute graph drawing column cell chord).head? =
      some (Cell.add (drawing.rectangleRouteOffset column cell) (chord.1.point drawing.paddedSlabWidth (paddedGridSize drawing.gridSize))) := by
  simp only [liftedRectangleInputRoute,rectangleInputRoute,matchingRoute,translatePolyline,List.head?_map,route_head,Option.map_some]

theorem liftedRectangleInputRoute_last {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (column : Nat) (cell : Cell) (chord : Chord) :
    (liftedRectangleInputRoute graph drawing column cell chord).getLast? =
      some (Cell.add (drawing.rectangleRouteOffset column cell) (chord.2.point drawing.paddedSlabWidth (paddedGridSize drawing.gridSize))) := by
  simp only [liftedRectangleInputRoute,rectangleInputRoute,matchingRoute,translatePolyline,List.getLast?_map,route_last,Option.map_some]

theorem liftedRectangleInputRoute_isRealOpenSimple {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {column : Nat} {chord : Chord} (member : chord ∈ rectangleChordFamily graph drawing column) (cell : Cell) :
    GridPolyline.IsRealOpenSimple (liftedRectangleInputRoute graph drawing column cell chord) :=
  (rectangleInputRoute_isRealOpenSimple planar degree graphLocal straight member).translate _

theorem liftedRectangleInputRoute_orthogonal {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {column : Nat} {chord : Chord} (member : chord ∈ rectangleChordFamily graph drawing column) (cell : Cell) :
    OrthogonalPolyline (liftedRectangleInputRoute graph drawing column cell chord) :=
  (rectangleInputRoute_orthogonal planar degree graphLocal straight member).translate _

theorem liftedRectangleInputRoute_real_bounds {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {column : Nat} {chord : Chord} (member : chord ∈ rectangleChordFamily graph drawing column) (cell : Cell) {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains (liftedRectangleInputRoute graph drawing column cell chord) point) :
    0 ≤ point.1-(drawing.rectangleRouteOffset column cell).1 ∧ point.1-(drawing.rectangleRouteOffset column cell).1 ≤ drawing.paddedSlabWidth ∧
      0 ≤ point.2-(drawing.rectangleRouteOffset column cell).2 ∧ point.2-(drawing.rectangleRouteOffset column cell).2 ≤ paddedGridSize drawing.gridSize :=
  rectangleInputRoute_real_bounds planar degree graphLocal straight member ((GridPolyline.realContains_translate_inverse _ _ _).mp contains)

theorem liftedRectangleInputRoute_boundary_contact_endpoint {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {column : Nat} {chord : Chord} (member : chord ∈ rectangleChordFamily graph drawing column) (cell : Cell) {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains (liftedRectangleInputRoute graph drawing column cell chord) point)
    (boundary : point.1-(drawing.rectangleRouteOffset column cell).1 = 0 ∨
      point.1-(drawing.rectangleRouteOffset column cell).1 = (drawing.paddedSlabWidth : ℝ) ∨
      point.2-(drawing.rectangleRouteOffset column cell).2 = 0 ∨
      point.2-(drawing.rectangleRouteOffset column cell).2 = (paddedGridSize drawing.gridSize : ℝ)) :
    GridPolyline.RealIsEndpoint (liftedRectangleInputRoute graph drawing column cell chord) point := by
  have contact := rectangleInputRoute_boundary_contact planar degree graphLocal straight member
    ((GridPolyline.realContains_translate_inverse _ _ _).mp contains) boundary
  rcases contact with atFirst | atLast
  · exact Or.inl ⟨_,liftedRectangleInputRoute_head graph drawing column cell chord,real_point_translate_back atFirst⟩
  · exact Or.inr ⟨_,liftedRectangleInputRoute_last graph drawing column cell chord,real_point_translate_back atLast⟩

end LeanTrominoes.PeriodicGridDrawing
