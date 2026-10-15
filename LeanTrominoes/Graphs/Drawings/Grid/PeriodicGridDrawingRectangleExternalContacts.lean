/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingPaddedIncidenceRoutes
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingPaddedCrossingBars
import LeanTrominoes.Graphs.Drawings.Grid.OrthogonalBoundaryStripSeparation

/-! # Rectangle contacts with crossing strips are confined to route endpoints -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement OrthogonalBoundaryRouting

theorem liftedRectangleInputRoute_column_strip_contact {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {column : Nat} {chord : Chord} (member : chord ∈ rectangleChordFamily graph drawing column) (cell : Cell) {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains (liftedRectangleInputRoute graph drawing column cell chord) point) (line : Int)
    (strip : |point.1-(paddedRefinementFactor drawing.gridSize : ℝ)*line| ≤ 5*(crossingBound drawing.gridSize : ℝ)) :
    (line = (drawing.rectangleRouteIndex column cell).1 ∧
      point.1 = (paddedRefinementFactor drawing.gridSize : ℝ)*(drawing.rectangleRouteIndex column cell).1+
        5*(crossingBound drawing.gridSize : ℝ)) ∨
      (line = (drawing.rectangleRouteIndex column cell).1+1 ∧
        point.1 = (paddedRefinementFactor drawing.gridSize : ℝ)*((drawing.rectangleRouteIndex column cell).1+1)-
          5*(crossingBound drawing.gridSize : ℝ)) := by
  have bounds := liftedRectangleInputRoute_real_bounds planar degree graphLocal straight member cell contains
  have spacing : 10*(crossingBound drawing.gridSize : Int) < paddedRefinementFactor drawing.gridSize := by
    simp only [paddedRefinementFactor,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat]
    have nonnegative : (0 : Int) ≤ crossingBound drawing.gridSize := by positivity
    omega
  have slab : (paddedRefinementFactor drawing.gridSize : ℝ)*(drawing.rectangleRouteIndex column cell).1+
      5*(crossingBound drawing.gridSize : ℝ) ≤ point.1 ∧
      point.1 ≤ (paddedRefinementFactor drawing.gridSize : ℝ)*((drawing.rectangleRouteIndex column cell).1+1)-
        5*(crossingBound drawing.gridSize : ℝ) := by
    simp only [rectangleRouteOffset,paddedSlabOrigin,paddedSlabWidth] at bounds
    push_cast at bounds
    constructor <;> linarith [bounds.1,bounds.2.1]
  have contact := strip_slab_contact_vertical_boundary spacing (by positivity) strip slab
  push_cast at contact
  exact contact

theorem liftedRectangleInputRoute_column_strip_contact_endpoint {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {column : Nat} {chord : Chord} (member : chord ∈ rectangleChordFamily graph drawing column) (cell : Cell) {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains (liftedRectangleInputRoute graph drawing column cell chord) point) (line : Int)
    (strip : |point.1-(paddedRefinementFactor drawing.gridSize : ℝ)*line| ≤ 5*(crossingBound drawing.gridSize : ℝ)) :
    GridPolyline.RealIsEndpoint (liftedRectangleInputRoute graph drawing column cell chord) point := by
  have contact := liftedRectangleInputRoute_column_strip_contact planar degree graphLocal straight member cell contains line strip
  apply liftedRectangleInputRoute_boundary_contact_endpoint planar degree graphLocal straight member cell contains
  rcases contact with ⟨_,atLeft⟩ | ⟨_,atRight⟩
  · left
    simp only [rectangleRouteOffset,paddedSlabOrigin]
    push_cast at atLeft ⊢
    linarith
  · right; left
    simp only [rectangleRouteOffset,paddedSlabOrigin,paddedSlabWidth]
    push_cast at atRight ⊢
    linarith

theorem liftedRectangleInputRoute_column_strip_contact_strip_boundary {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {column : Nat} {chord : Chord} (member : chord ∈ rectangleChordFamily graph drawing column) (cell : Cell) {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains (liftedRectangleInputRoute graph drawing column cell chord) point) (line : Int)
    (strip : |point.1-(paddedRefinementFactor drawing.gridSize : ℝ)*line| ≤ 5*(crossingBound drawing.gridSize : ℝ)) :
    point.1-(paddedRefinementFactor drawing.gridSize : ℝ)*line = -5*(crossingBound drawing.gridSize : ℝ) ∨
      point.1-(paddedRefinementFactor drawing.gridSize : ℝ)*line = 5*(crossingBound drawing.gridSize : ℝ) := by
  have contact := liftedRectangleInputRoute_column_strip_contact planar degree graphLocal straight member cell contains line strip
  rcases contact with ⟨same,atLeft⟩ | ⟨same,atRight⟩
  · right
    rw [same]
    linarith
  · left
    rw [same]
    push_cast
    linarith
theorem liftedRectangleInputRoute_crossing_bar_contact_endpoint {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {column : Nat} {chord : Chord} (member : chord ∈ rectangleChordFamily graph drawing column) (cell : Cell) {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains (liftedRectangleInputRoute graph drawing column cell chord) point) (line ordinate : Int)
    (barContains : GridPolyline.RealContains
      (enlargedCrossingBar (paddedRefinementFactor drawing.gridSize) (crossingBound drawing.gridSize) line ordinate) point) :
    GridPolyline.RealIsEndpoint (liftedRectangleInputRoute graph drawing column cell chord) point :=
  liftedRectangleInputRoute_column_strip_contact_endpoint planar degree graphLocal straight member cell contains line
    (enlargedCrossingBar_real_bounds _ _ _ _ barContains).1

theorem liftedRectangleInputRoute_vertex_fan_contact_endpoint {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {column : Nat} {chord : Chord} (member : chord ∈ rectangleChordFamily graph drawing column) (cell : Cell) {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains (liftedRectangleInputRoute graph drawing column cell chord) point)
    (position : Cell) (profile : AnchorProfile) (index : Fin 4)
    (fanContains : GridPolyline.RealContains
      (enlargedRectangleTemplate (paddedRefinementFactor drawing.gridSize) (crossingBound drawing.gridSize) position profile index) point) :
    GridPolyline.RealIsEndpoint (liftedRectangleInputRoute graph drawing column cell chord) point :=
  liftedRectangleInputRoute_column_strip_contact_endpoint planar degree graphLocal straight member cell contains position.1
    (enlargedRectangleTemplate_real_bounds _ _ _ _ _ fanContains).1

end LeanTrominoes.PeriodicGridDrawing
