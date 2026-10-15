/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingRectanglePortContactParents
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingOrientedRectangleRoutes
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingRectangleRouteSeparation

/-! # Contacts between rectangle routes identify their original lifted edge -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement OrthogonalBoundaryRouting

theorem rectangleParentChord_integral_parent_injective {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (column : Nat) (firstParent lastParent : Nat × Cell)
    {first last : RectanglePortKey Vertex × RectanglePortKey Vertex}
    (firstLookup : rectangleParentChord graph drawing column firstParent = some first)
    (lastLookup : rectangleParentChord graph drawing column lastParent = some last)
    (chordEq : (first.1.integralPort graph drawing column,first.2.integralPort graph drawing column) =
      (last.1.integralPort graph drawing column,last.2.integralPort graph drawing column)) : firstParent = lastParent := by
  have firstData := rectangleParentChord_data graph drawing column firstParent firstLookup
  have lastData := rectangleParentChord_data graph drawing column lastParent lastLookup
  have portEq := congrArg Prod.fst chordEq
  by_contra different
  have parentsDifferent : first.1.parentKey ≠ last.1.parentKey := by
    rw [firstData.2.2.1,lastData.2.2.1]
    exact different
  have oldDifferent := rectanglePort_ne_of_parent_ne planar straight column
    (first := first.1) (last := last.1) firstData.1 lastData.1 parentsDifferent
  exact RectangleBoundaryMatchingTransport.new_ports_ne_of_old_ports_ne
    (Key := RectanglePortKey Vertex)
    (valid := fun key => key.Valid graph drawing column)
    (oldPort := fun key => key.virtualPort graph drawing column)
    (newPort := fun key => key.integralPort graph drawing column)
    (fun _ fv _ lv ordered => rectanglePort_preserves_before planar degree graphLocal straight column fv lv ordered)
    firstData.1 lastData.1 oldDifferent portEq

theorem liftedRectangleParentRoute_endpoint_key {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (column : Nat) (cell : Cell) (parent : Nat × Cell)
    {keys : RectanglePortKey Vertex × RectanglePortKey Vertex}
    (lookup : rectangleParentChord graph drawing column parent = some keys) {point : ℝ × ℝ}
    (endpoint : GridPolyline.RealIsEndpoint (liftedRectangleInputRoute graph drawing column cell
      (keys.1.integralPort graph drawing column,keys.2.integralPort graph drawing column)) point) :
    ∃ key : RectanglePortKey Vertex, key.Valid graph drawing column ∧ key.parentKey = parent ∧
      point = realCell (rectangleLiftedPortPoint graph drawing column cell key) := by
  have data := rectangleParentChord_data graph drawing column parent lookup
  rcases endpoint with ⟨value,head,pointEq⟩ | ⟨value,last,pointEq⟩
  · have valueEq := Option.some.inj (head.symm.trans (liftedRectangleInputRoute_head graph drawing column cell _))
    exact ⟨keys.1,data.1,data.2.2.1,by simpa only [valueEq,rectangleLiftedPortPoint] using pointEq⟩
  · have valueEq := Option.some.inj (last.symm.trans (liftedRectangleInputRoute_last graph drawing column cell _))
    exact ⟨keys.2,data.2.1,data.2.2.2.1,by simpa only [valueEq,rectangleLiftedPortPoint] using pointEq⟩

theorem liftedRectangleParentRoutes_contact_parent_eq {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (firstColumn lastColumn : Nat) (firstBound : firstColumn < drawing.gridSize) (lastBound : lastColumn < drawing.gridSize)
    (firstCell lastCell : Cell) (firstParent lastParent : Nat × Cell)
    {first last : RectanglePortKey Vertex × RectanglePortKey Vertex}
    (firstLookup : rectangleParentChord graph drawing firstColumn firstParent = some first)
    (lastLookup : rectangleParentChord graph drawing lastColumn lastParent = some last)
    {point : ℝ × ℝ}
    (firstContains : GridPolyline.RealContains (liftedRectangleInputRoute graph drawing firstColumn firstCell
      (first.1.integralPort graph drawing firstColumn,first.2.integralPort graph drawing firstColumn)) point)
    (lastContains : GridPolyline.RealContains (liftedRectangleInputRoute graph drawing lastColumn lastCell
      (last.1.integralPort graph drawing lastColumn,last.2.integralPort graph drawing lastColumn)) point) :
    (firstParent.1,Cell.add firstParent.2 firstCell) = (lastParent.1,Cell.add lastParent.2 lastCell) := by
  have firstMember := rectangleParentChord_mem_family planar.1.1 graphLocal straight firstColumn firstParent firstLookup
  have lastMember := rectangleParentChord_mem_family planar.1.1 graphLocal straight lastColumn lastParent lastLookup
  by_cases same : (firstColumn,firstCell) = (lastColumn,lastCell)
  · have columns := congrArg Prod.fst same
    have cells := congrArg Prod.snd same
    change firstColumn = lastColumn at columns
    change firstCell = lastCell at cells
    subst lastColumn
    subst lastCell
    have chordEq : (first.1.integralPort graph drawing firstColumn,first.2.integralPort graph drawing firstColumn) =
        (last.1.integralPort graph drawing firstColumn,last.2.integralPort graph drawing firstColumn) := by
      by_contra different
      exact liftedRectangleInputRoutes_same_cell_disjoint planar degree graphLocal straight firstMember lastMember different firstCell firstContains lastContains
    have parents := rectangleParentChord_integral_parent_injective planar degree graphLocal straight firstColumn firstParent lastParent firstLookup lastLookup chordEq
    rw [parents]
  have firstEndpoint := liftedRectangleInputRoutes_distinct_cells_contact_endpoint planar degree graphLocal straight
    firstBound lastBound firstMember lastMember firstCell lastCell same firstContains lastContains
  have lastEndpoint := liftedRectangleInputRoutes_distinct_cells_contact_endpoint planar degree graphLocal straight
    lastBound firstBound lastMember firstMember lastCell firstCell (Ne.symm same) lastContains firstContains
  obtain ⟨firstKey,firstValid,firstKeyParent,firstPoint⟩ := liftedRectangleParentRoute_endpoint_key firstColumn firstCell firstParent firstLookup firstEndpoint
  obtain ⟨lastKey,lastValid,lastKeyParent,lastPoint⟩ := liftedRectangleParentRoute_endpoint_key lastColumn lastCell lastParent lastLookup lastEndpoint
  have points := realCell_injective (firstPoint.symm.trans lastPoint)
  have parents := rectangle_integral_ports_contact_parent_eq planar degree graphLocal straight
    firstColumn lastColumn firstBound lastBound firstCell lastCell firstValid lastValid points
  simpa only [RectanglePortKey.liftedParentKey,firstKeyParent,lastKeyParent] using parents

end LeanTrominoes.PeriodicGridDrawing
