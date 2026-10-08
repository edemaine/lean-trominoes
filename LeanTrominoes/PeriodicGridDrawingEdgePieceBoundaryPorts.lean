/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingEdgePieceEnumeration
import LeanTrominoes.PeriodicGridDrawingRectanglePortParameterPoints

/-! # Computed entry and exit rectangle ports agree with the oriented interval endpoints -/
namespace LeanTrominoes.PeriodicGridDrawing
open PeriodicOrthocrossing OrthogonalDrawingRefinement

theorem orientedRectangleInputRoute_endpoint_parameters {Vertex : Type*}
    (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) (column : Nat) (parent : Nat × Cell)
    (first last : RectanglePortKey Vertex) :
    rectanglePortParentParameter graph drawing column parent
        (if rectangleParentForward graph drawing column parent first last then first else last) =
      min (rectanglePortParentParameter graph drawing column parent first) (rectanglePortParentParameter graph drawing column parent last) ∧
    rectanglePortParentParameter graph drawing column parent
        (if rectangleParentForward graph drawing column parent first last then last else first) =
      max (rectanglePortParentParameter graph drawing column parent first) (rectanglePortParentParameter graph drawing column parent last) := by
  by_cases forward : rectangleParentForward graph drawing column parent first last
  · have order : rectanglePortParentParameter graph drawing column parent first ≤
        rectanglePortParentParameter graph drawing column parent last := forward.le
    simp only [if_pos forward,min_eq_left order,max_eq_right order,and_self]
  · have order : rectanglePortParentParameter graph drawing column parent last ≤
        rectanglePortParentParameter graph drawing column parent first := le_of_not_gt forward
    simp only [if_neg forward,min_eq_right order,max_eq_left order,and_self]

theorem rectangleEdgePiece?_boundary_ports {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (index column : Nat) (cell : Cell) {piece : EdgeRoutePiece}
    (lookup : rectangleEdgePiece? graph drawing index column cell = some piece)
    {first last : RectanglePortKey Vertex}
    (chord : rectangleParentChord graph drawing column (index,Cell.scale (-1) cell) = some (first,last)) :
    piece.route.head? = some (Cell.add (drawing.rectangleRouteOffset column cell)
      ((if rectangleParentForward graph drawing column (index,Cell.scale (-1) cell) first last then first else last).integralPort graph drawing column
        |>.point drawing.paddedSlabWidth (paddedGridSize drawing.gridSize))) ∧
    piece.route.getLast? = some (Cell.add (drawing.rectangleRouteOffset column cell)
      ((if rectangleParentForward graph drawing column (index,Cell.scale (-1) cell) first last then last else first).integralPort graph drawing column
        |>.point drawing.paddedSlabWidth (paddedGridSize drawing.gridSize))) ∧
    piece.start = rectanglePortParentParameter graph drawing column (index,Cell.scale (-1) cell)
      (if rectangleParentForward graph drawing column (index,Cell.scale (-1) cell) first last then first else last) ∧
    piece.finish = rectanglePortParentParameter graph drawing column (index,Cell.scale (-1) cell)
      (if rectangleParentForward graph drawing column (index,Cell.scale (-1) cell) first last then last else first) := by
  unfold rectangleEdgePiece? at lookup
  have pieceEq := Option.some.inj (by simpa only [chord,Option.map_some] using lookup)
  subst piece
  have parameters := orientedRectangleInputRoute_endpoint_parameters graph drawing column (index,Cell.scale (-1) cell) first last
  refine ⟨?_,?_,parameters.1.symm,parameters.2.symm⟩
  · simp only [translatePolyline,List.head?_map,orientedRectangleInputRoute_head,Option.map_some]
  · simp only [translatePolyline,List.getLast?_map,orientedRectangleInputRoute_last,Option.map_some]

theorem rectangleEdgePiece?_endpoint_original_points {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (index column : Nat) (cell : Cell) {piece : EdgeRoutePiece}
    (lookup : rectangleEdgePiece? graph drawing index column cell = some piece)
    {first last : RectanglePortKey Vertex}
    (chord : rectangleParentChord graph drawing column (index,Cell.scale (-1) cell) = some (first,last)) :
    (drawing.liftedStraightSegment index (0,0)).rationalPointAtParameter piece.start =
      rectanglePortOriginalPoint graph drawing column cell
        (if rectangleParentForward graph drawing column (index,Cell.scale (-1) cell) first last then first else last) ∧
    (drawing.liftedStraightSegment index (0,0)).rationalPointAtParameter piece.finish =
      rectanglePortOriginalPoint graph drawing column cell
        (if rectangleParentForward graph drawing column (index,Cell.scale (-1) cell) first last then last else first) := by
  have ports := rectangleEdgePiece?_boundary_ports index column cell lookup chord
  have data := rectangleParentChord_data graph drawing column (index,Cell.scale (-1) cell) chord
  rw [ports.2.2.1,ports.2.2.2]
  by_cases forward : rectangleParentForward graph drawing column (index,Cell.scale (-1) cell) first last
  · simp only [if_pos forward]
    exact ⟨rectanglePort_prototype_parameter_point planar graphLocal straight index column cell data.1 data.2.2.1,
      rectanglePort_prototype_parameter_point planar graphLocal straight index column cell data.2.1 data.2.2.2.1⟩
  · simp only [if_neg forward]
    exact ⟨rectanglePort_prototype_parameter_point planar graphLocal straight index column cell data.2.1 data.2.2.2.1,
      rectanglePort_prototype_parameter_point planar graphLocal straight index column cell data.1 data.2.2.1⟩

end LeanTrominoes.PeriodicGridDrawing
