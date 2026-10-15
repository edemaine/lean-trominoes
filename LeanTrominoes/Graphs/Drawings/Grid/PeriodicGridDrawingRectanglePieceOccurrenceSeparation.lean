/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingRectangleRouteContactParents
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingRectanglePieceRawRoutes

/-! # Rectangle pieces of distinct periodic edge occurrences are disjoint -/
namespace LeanTrominoes.PeriodicGridDrawing
open PeriodicOrthocrossing OrthogonalDrawingRefinement

theorem liftedRectangleInputRoute_add_cell {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) (column : Nat) (cell shift : Cell) (chord : OrthogonalBoundaryRouting.Chord) :
    liftedRectangleInputRoute graph drawing column (Cell.add cell shift) chord =
      translatePolyline (Cell.scale (paddedGridSize drawing.gridSize) shift)
        (liftedRectangleInputRoute graph drawing column cell chord) := by
  simp only [liftedRectangleInputRoute,translatePolyline,List.map_map]
  apply List.map_congr_left
  intro point _
  apply Prod.ext <;> simp [rectangleRouteOffset,rectangleRouteIndex,paddedSlabOrigin,Cell.add,Cell.scale,paddedGridSize] <;> ring

theorem rectangleEdgePiece?_translated_raw_image {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (index column : Nat) (cell shift : Cell) {piece : EdgeRoutePiece}
    (lookup : rectangleEdgePiece? graph drawing index column cell = some piece)
    {keys : RectanglePortKey Vertex × RectanglePortKey Vertex}
    (chord : rectangleParentChord graph drawing column (index,Cell.scale (-1) cell) = some keys)
    (point : ℝ × ℝ) :
    GridPolyline.RealContains (translatePolyline (Cell.scale (paddedGridSize drawing.gridSize) shift) piece.route) point ↔
      GridPolyline.RealContains (liftedRectangleInputRoute graph drawing column (Cell.add cell shift)
        (keys.1.integralPort graph drawing column,keys.2.integralPort graph drawing column)) point := by
  rw [liftedRectangleInputRoute_add_cell,GridPolyline.realContains_translate_inverse,GridPolyline.realContains_translate_inverse]
  exact (rectangleEdgePiece?_raw_image_endpoints index column cell lookup chord _).1

theorem rectangleEdgePiece_occurrences_contact_eq {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (firstIndex lastIndex firstColumn lastColumn : Nat)
    (firstBound : firstColumn < drawing.gridSize) (lastBound : lastColumn < drawing.gridSize)
    (firstCell lastCell firstShift lastShift : Cell) {first last : EdgeRoutePiece}
    (firstLookup : rectangleEdgePiece? graph drawing firstIndex firstColumn firstCell = some first)
    (lastLookup : rectangleEdgePiece? graph drawing lastIndex lastColumn lastCell = some last)
    {point : ℝ × ℝ}
    (firstContains : GridPolyline.RealContains (translatePolyline (Cell.scale (paddedGridSize drawing.gridSize) firstShift) first.route) point)
    (lastContains : GridPolyline.RealContains (translatePolyline (Cell.scale (paddedGridSize drawing.gridSize) lastShift) last.route) point) :
    (firstIndex,firstShift) = (lastIndex,lastShift) := by
  cases firstChord : rectangleParentChord graph drawing firstColumn (firstIndex,Cell.scale (-1) firstCell) with
  | none => simp [rectangleEdgePiece?,firstChord] at firstLookup
  | some firstKeys =>
    cases lastChord : rectangleParentChord graph drawing lastColumn (lastIndex,Cell.scale (-1) lastCell) with
    | none => simp [rectangleEdgePiece?,lastChord] at lastLookup
    | some lastKeys =>
      have parents := liftedRectangleParentRoutes_contact_parent_eq planar degree graphLocal straight firstColumn lastColumn firstBound lastBound
        (Cell.add firstCell firstShift) (Cell.add lastCell lastShift) (firstIndex,Cell.scale (-1) firstCell) (lastIndex,Cell.scale (-1) lastCell)
        firstChord lastChord
        ((rectangleEdgePiece?_translated_raw_image firstIndex firstColumn firstCell firstShift firstLookup firstChord point).mp firstContains)
        ((rectangleEdgePiece?_translated_raw_image lastIndex lastColumn lastCell lastShift lastLookup lastChord point).mp lastContains)
      simpa [Cell.add,Cell.scale,add_assoc] using parents

end LeanTrominoes.PeriodicGridDrawing
