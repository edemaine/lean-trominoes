/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRectangleInputMatching
import LeanTrominoes.OrthogonalBoundaryArcBounds

/-! # The assembled finite input matching yields simple disjoint orthogonal routes -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement OrthogonalBoundaryRouting PeriodicOrthocrossing

def rectangleInputRoute {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (column : Nat) (chord : Chord) : List Cell :=
  matchingRoute (rectangleChordFamily graph drawing column) drawing.paddedSlabWidth (paddedGridSize drawing.gridSize) chord

theorem rectangleInputRoute_orthogonal {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {column : Nat} {chord : Chord} (member : chord ∈ rectangleChordFamily graph drawing column) :
    OrthogonalPolyline (rectangleInputRoute graph drawing column chord) := by
  have valid := rectangleChordFamily_valid planar degree graphLocal straight member
  exact matchingRoute_orthogonal member (rectangleChordFamily_room planar.1.1 degree column) valid.1 valid.2.1 valid.2.2

theorem rectangleInputRoute_isRealOpenSimple {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {column : Nat} {chord : Chord} (member : chord ∈ rectangleChordFamily graph drawing column) :
    GridPolyline.IsRealOpenSimple (rectangleInputRoute graph drawing column chord) := by
  have valid := rectangleChordFamily_valid planar degree graphLocal straight member
  exact matchingRoute_isRealOpenSimple member (rectangleChordFamily_room planar.1.1 degree column) valid.1 valid.2.1 valid.2.2

theorem rectangleInputRoutes_disjoint {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {column : Nat} {first last : Chord} (firstMember : first ∈ rectangleChordFamily graph drawing column)
    (lastMember : last ∈ rectangleChordFamily graph drawing column) (different : first ≠ last) {point : ℝ × ℝ}
    (firstContains : GridPolyline.RealContains (rectangleInputRoute graph drawing column first) point)
    (lastContains : GridPolyline.RealContains (rectangleInputRoute graph drawing column last) point) : False := by
  have firstValid := rectangleChordFamily_valid planar degree graphLocal straight firstMember
  have lastValid := rectangleChordFamily_valid planar degree graphLocal straight lastMember
  exact matchingRoutes_disjoint firstMember lastMember different (rectangleChordFamily_room planar.1.1 degree column)
    firstValid.1 firstValid.2.1 lastValid.1 lastValid.2.1 firstValid.2.2 lastValid.2.2
    (rectangleChordFamily_noninterlacing planar degree graphLocal straight firstMember lastMember different) firstContains lastContains

theorem rectangleInputRoute_real_bounds {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {column : Nat} {chord : Chord} (member : chord ∈ rectangleChordFamily graph drawing column) {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains (rectangleInputRoute graph drawing column chord) point) :
    (0 : ℝ) ≤ point.1 ∧ point.1 ≤ drawing.paddedSlabWidth ∧ (0 : ℝ) ≤ point.2 ∧ point.2 ≤ paddedGridSize drawing.gridSize := by
  have valid := rectangleChordFamily_valid planar degree graphLocal straight member
  exact route_real_bounds (by exact_mod_cast matchingDepth_positive (rectangleChordFamily graph drawing column) chord)
    (by exact_mod_cast matchingDepth_le_card member) (rectangleChordFamily_room planar.1.1 degree column) valid.1 valid.2.1 contains

theorem rectangleInputRoute_boundary_contact {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {column : Nat} {chord : Chord} (member : chord ∈ rectangleChordFamily graph drawing column) {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains (rectangleInputRoute graph drawing column chord) point)
    (boundary : point.1 = 0 ∨ point.1 = (drawing.paddedSlabWidth : ℝ) ∨ point.2 = 0 ∨ point.2 = (paddedGridSize drawing.gridSize : ℝ)) :
    point = realCell (chord.1.point drawing.paddedSlabWidth (paddedGridSize drawing.gridSize)) ∨
      point = realCell (chord.2.point drawing.paddedSlabWidth (paddedGridSize drawing.gridSize)) := by
  have valid := rectangleChordFamily_valid planar degree graphLocal straight member
  exact route_boundary_contact_ports (by exact_mod_cast matchingDepth_positive (rectangleChordFamily graph drawing column) chord)
    (by exact_mod_cast matchingDepth_le_card member) (rectangleChordFamily_room planar.1.1 degree column)
    valid.1 valid.2.1 valid.2.2 contains boundary

end LeanTrominoes.PeriodicGridDrawing
