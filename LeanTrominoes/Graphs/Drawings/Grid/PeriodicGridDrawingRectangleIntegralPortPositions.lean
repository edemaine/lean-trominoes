/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.OrthogonalBoundaryPortPointFaces
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingRectangleRowPortJoins

/-! # The new integral position identifies each proper rectangle-port face -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement OrthogonalBoundaryRouting

theorem rectangleIntegralPort_point_bounds_faces {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (column : Nat) {key : RectanglePortKey Vertex} (valid : key.Valid graph drawing column) :
    let point := (key.integralPort graph drawing column).point drawing.paddedSlabWidth (paddedGridSize drawing.gridSize)
    (0 ≤ point.1 ∧ point.1 ≤ drawing.paddedSlabWidth) ∧
    (0 ≤ point.2 ∧ point.2 ≤ paddedGridSize drawing.gridSize) ∧
    (point.1 = 0 ↔ key.side.val = 0) ∧
    (point.1 = drawing.paddedSlabWidth ↔ key.side.val = 2) ∧
    (point.2 = 0 ↔ key.side.val = 3) ∧
    (point.2 = paddedGridSize drawing.gridSize ↔ key.side.val = 1) := by
  have room := paddedSlab_room drawing
  have nonnegative : (0 : Int) ≤ crossingBound drawing.gridSize := by positivity
  have faces := Port.point_bounds_faces (by omega : 0 < drawing.paddedSlabWidth)
    (by omega : (0 : Int) < paddedGridSize drawing.gridSize) (by positivity : (0 : Int) ≤ 2*crossingBound drawing.gridSize)
    (rectanglePort_integral_inside planar degree graphLocal straight column valid)
  simpa only [rectanglePort_integral_side] using faces

theorem rectanglePort_vertical_of_integral_face {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (column : Nat) (cell : Cell) (right : Bool) {key : RectanglePortKey Vertex} (valid : key.Valid graph drawing column)
    (contact : (rectangleLiftedPortPoint graph drawing column cell key).1 =
      (drawing.rectangleRouteOffset column cell).1+(if right then drawing.paddedSlabWidth else 0)) :
    ∃ raw : ColumnPortKey Vertex, key = .vertical right raw := by
  have faces := rectangleIntegralPort_point_bounds_faces planar degree graphLocal straight column valid
  have localContact : ((key.integralPort graph drawing column).point drawing.paddedSlabWidth (paddedGridSize drawing.gridSize)).1 =
      if right then drawing.paddedSlabWidth else 0 := by
    change (drawing.rectangleRouteOffset column cell).1+_ = _ at contact
    omega
  have sideEq : key.side.val = if right then 2 else 0 := by
    cases right
    · exact faces.2.2.1.mp localContact
    · exact faces.2.2.2.1.mp localContact
  cases key with
  | vertical own raw =>
    have ownEq : own = right := by cases own <;> cases right <;> simp_all [RectanglePortKey.side]
    subst own
    exact ⟨raw,rfl⟩
  | horizontal top raw => cases top <;> cases right <;> norm_num [RectanglePortKey.side] at sideEq

theorem rectanglePort_horizontal_of_integral_face {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (column : Nat) (cell : Cell) (top : Bool) {key : RectanglePortKey Vertex} (valid : key.Valid graph drawing column)
    (contact : (rectangleLiftedPortPoint graph drawing column cell key).2 =
      (drawing.rectangleRouteOffset column cell).2+(if top then (paddedGridSize drawing.gridSize : Int) else 0)) :
    ∃ raw : Nat × Cell, key = .horizontal top raw := by
  have faces := rectangleIntegralPort_point_bounds_faces planar degree graphLocal straight column valid
  have localContact : ((key.integralPort graph drawing column).point drawing.paddedSlabWidth (paddedGridSize drawing.gridSize)).2 =
      if top then (paddedGridSize drawing.gridSize : Int) else 0 := by
    change (drawing.rectangleRouteOffset column cell).2+_ = _ at contact
    omega
  have sideEq : key.side.val = if top then 1 else 3 := by
    cases top
    · exact faces.2.2.2.2.1.mp localContact
    · exact faces.2.2.2.2.2.mp localContact
  cases key with
  | vertical right raw => cases right <;> cases top <;> norm_num [RectanglePortKey.side] at sideEq
  | horizontal own raw =>
    have ownEq : own = top := by cases own <;> cases top <;> simp_all [RectanglePortKey.side]
    subst own
    exact ⟨raw,rfl⟩

end LeanTrominoes.PeriodicGridDrawing
