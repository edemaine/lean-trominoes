/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingRectangleClipCoverage
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingRectanglePortCopyWindow

/-! # Every retained original edge port is covered by the assembled matching -/
namespace LeanTrominoes.PeriodicGridDrawing

theorem rectangleParentChord_covers_port {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) (column : Nat)
    {key first last : RectanglePortKey Vertex} (valid : key.Valid graph drawing column)
    (lookup : rectangleParentChord graph drawing column key.parentKey = some (first,last)) :
    key.virtualPort graph drawing column = first.virtualPort graph drawing column ∨
      key.virtualPort graph drawing column = last.virtualPort graph drawing column := by
  obtain ⟨representative,member,equal⟩ := rectangleParentPorts_cover graph drawing column key.parentKey valid rfl
  have ports := (rectangleParentChord_some_iff graph drawing column key.parentKey first last).mp lookup
  rw [ports] at member
  rcases List.mem_cons.mp member with rfl | member
  · exact Or.inl equal.symm
  · have lastEqual := List.mem_singleton.mp member
    subst representative
    exact Or.inr equal.symm

theorem rectangleChordFamily_covers_port {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (column : Nat) (columnBound : column < drawing.gridSize) {key : RectanglePortKey Vertex} (valid : key.Valid graph drawing column) :
    ∃ first last : RectanglePortKey Vertex,
      rectangleParentChord graph drawing column key.parentKey = some (first,last) ∧
      (first.integralPort graph drawing column,last.integralPort graph drawing column) ∈ rectangleChordFamily graph drawing column ∧
      (key.virtualPort graph drawing column = first.virtualPort graph drawing column ∨
        key.virtualPort graph drawing column = last.virtualPort graph drawing column) := by
  obtain ⟨first,last,lookup⟩ := rectangleParentChord_exists_of_port planar graphLocal straight column columnBound valid
  have parentAt := rectanglePort_parent_mem_nineEdgeCopies planar.1.1 graphLocal straight valid
  have keysAt : (first,last) ∈ rectangleChordKeys graph drawing column := List.mem_filterMap.mpr ⟨key.parentKey,parentAt,lookup⟩
  refine ⟨first,last,lookup,?_,rectangleParentChord_covers_port graph drawing column valid lookup⟩
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨(first,last),keysAt,rfl⟩)

end LeanTrominoes.PeriodicGridDrawing
