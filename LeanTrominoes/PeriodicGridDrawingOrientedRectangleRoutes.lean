/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRectangleParameterIntervals
import LeanTrominoes.PeriodicGridDrawingRectanglePortJoins
import LeanTrominoes.PeriodicGridDrawingRectanglePortCopyWindow
import LeanTrominoes.GridPolylineRealOpenReverse
import LeanTrominoes.OrthogonalPolylineSymmetries

/-! # Computed rectangle routes follow the direction of their original edge -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement OrthogonalBoundaryRouting

def rectangleParentForward {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (column : Nat) (parent : Nat × Cell) (first last : RectanglePortKey Vertex) : Prop :=
  rectanglePortParentParameter graph drawing column parent first < rectanglePortParentParameter graph drawing column parent last

instance {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (column : Nat) (parent : Nat × Cell) (first last : RectanglePortKey Vertex) :
    Decidable (rectangleParentForward graph drawing column parent first last) := inferInstanceAs (Decidable (_ < (_ : ℚ)))

def orientedRectangleInputRoute {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (column : Nat) (parent : Nat × Cell) (first last : RectanglePortKey Vertex) : List Cell :=
  let route := rectangleInputRoute graph drawing column (first.integralPort graph drawing column,last.integralPort graph drawing column)
  if rectangleParentForward graph drawing column parent first last then route else route.reverse

theorem rectangleParentChord_mem_family {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible graph) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (column : Nat) (parent : Nat × Cell) {first last : RectanglePortKey Vertex}
    (lookup : rectangleParentChord graph drawing column parent = some (first,last)) :
    (first.integralPort graph drawing column,last.integralPort graph drawing column) ∈ rectangleChordFamily graph drawing column := by
  have data := rectangleParentChord_data graph drawing column parent lookup
  have parentMember := rectanglePort_parent_mem_nineEdgeCopies compatible graphLocal straight data.1
  rw [data.2.2.1] at parentMember
  apply List.mem_toFinset.mpr
  apply List.mem_map.mpr
  refine ⟨(first,last),?_,rfl⟩
  exact List.mem_filterMap.mpr ⟨parent,parentMember,lookup⟩

theorem orientedRectangleInputRoute_valid {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (column : Nat) (parent : Nat × Cell) {first last : RectanglePortKey Vertex}
    (lookup : rectangleParentChord graph drawing column parent = some (first,last)) :
    GridPolyline.IsRealOpenSimple (orientedRectangleInputRoute graph drawing column parent first last) ∧
      PeriodicOrthocrossing.OrthogonalPolyline (orientedRectangleInputRoute graph drawing column parent first last) := by
  have member := rectangleParentChord_mem_family planar.1.1 graphLocal straight column parent lookup
  have simple := rectangleInputRoute_isRealOpenSimple planar degree graphLocal straight member
  have orthogonal := rectangleInputRoute_orthogonal planar degree graphLocal straight member
  unfold orientedRectangleInputRoute
  split_ifs
  · exact ⟨simple,orthogonal⟩
  · exact ⟨simple.reverse,orthogonal.reverse⟩

theorem orientedRectangleInputRoute_head {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) (column : Nat) (parent : Nat × Cell) (first last : RectanglePortKey Vertex) :
    (orientedRectangleInputRoute graph drawing column parent first last).head? =
      some ((if rectangleParentForward graph drawing column parent first last then first else last).integralPort graph drawing column |>.point drawing.paddedSlabWidth (paddedGridSize drawing.gridSize)) := by
  unfold orientedRectangleInputRoute
  split_ifs <;> simp only [rectangleInputRoute,matchingRoute,List.head?_reverse,route_head,route_last]

theorem orientedRectangleInputRoute_last {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) (column : Nat) (parent : Nat × Cell) (first last : RectanglePortKey Vertex) :
    (orientedRectangleInputRoute graph drawing column parent first last).getLast? =
      some ((if rectangleParentForward graph drawing column parent first last then last else first).integralPort graph drawing column |>.point drawing.paddedSlabWidth (paddedGridSize drawing.gridSize)) := by
  unfold orientedRectangleInputRoute
  split_ifs <;> simp only [rectangleInputRoute,matchingRoute,List.getLast?_reverse,route_head,route_last]

theorem orientedRectangleInputRoute_realContains {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) (column : Nat) (parent : Nat × Cell) (first last : RectanglePortKey Vertex) (point : ℝ × ℝ) :
    GridPolyline.RealContains (orientedRectangleInputRoute graph drawing column parent first last) point ↔
      GridPolyline.RealContains (rectangleInputRoute graph drawing column (first.integralPort graph drawing column,last.integralPort graph drawing column)) point := by
  unfold orientedRectangleInputRoute
  split_ifs
  · rfl
  · exact GridPolyline.realContains_reverse _ _

end LeanTrominoes.PeriodicGridDrawing
