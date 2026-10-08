/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRectangleStripContactKeys
import LeanTrominoes.PeriodicGridDrawingRectanglePortPhysicalPieces
import LeanTrominoes.PeriodicGridDrawingPaddedCrossingSeparation
import LeanTrominoes.PeriodicGridDrawingRectanglePieceOccurrenceSeparation

/-! # A rectangle meeting a proper crossing bar belongs to the same old edge occurrence -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement PeriodicOrthocrossing GeneralVertexNormalization

theorem liftedRectangleParentRoute_bar_contact_parent_eq {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (column : Nat) (cell : Cell) (parent : Nat × Cell)
    {keys : RectanglePortKey Vertex × RectanglePortKey Vertex}
    (lookup : rectangleParentChord graph drawing column parent = some keys)
    {barEdge : PeriodicEdge Vertex × Nat} (barMember : barEdge ∈ graph.edges.zipIdx)
    (barCell : Cell) (line : Int) (crosses : (drawing.liftedStraightSegment barEdge.2 barCell).CrossesVerticalLine line)
    {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains (liftedRectangleInputRoute graph drawing column cell
      (keys.1.integralPort graph drawing column,keys.2.integralPort graph drawing column)) point)
    (barContains : GridPolyline.RealContains (paddedCrossingRoute graph drawing line (barEdge.2,barCell)) point) :
    (parent.1,Cell.add parent.2 cell) = (barEdge.2,barCell) := by
  obtain ⟨right,raw,valid,keyParent,pointEq,lineEq⟩ := liftedRectangleParentRoute_strip_contact_key
    planar degree graphLocal straight column cell parent lookup contains line
    (enlargedCrossingBar_real_bounds _ _ _ _ barContains).1
  cases raw with
  | crossing key =>
    obtain ⟨rectangleEdge,rectangleMember,indexEq⟩ := rectanglePort_parent_tagged valid
    change rectangleEdge.2 = key.1 at indexEq
    have onBar := rectangle_crossing_port_on_bar graph drawing column cell right key
    rw [← pointEq,← lineEq] at onBar
    have rectangleCrosses := rectangle_crossing_port_lifted_crosses column cell right valid
    rw [← lineEq,← indexEq] at rectangleCrosses
    rw [← indexEq] at onBar
    have parents := (paddedCrossingRoutes_contact_identifies_occurrence planar degree graphLocal straight
      rectangleMember barMember (Cell.add key.2 cell) barCell rectangleCrosses crosses onBar barContains).2
    simpa only [← keyParent,RectanglePortKey.parentKey,ColumnPortKey.parentKey,indexEq] using parents
  | incidence tagged target =>
    have onFan := rectangle_incidence_port_on_fan planar degree straight column cell right valid
    rw [← pointEq] at onFan
    have crossing := periodic_crossing_residue_mem planar.1.1 barMember (straight _ barMember)
      (graphLocal _ (List.fst_mem_of_mem_zipIdx barMember)) barCell crosses
    exact (paddedCrossingBar_avoids_incidence_route planar.1.1 degree crossing
      (endpointPort_mem graph valid.1 target) cell barContains onFan).elim

theorem rectangleEdgePiece_bar_contact_occurrence_eq {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (index column : Nat) (cell shift : Cell) {piece : EdgeRoutePiece}
    (lookup : rectangleEdgePiece? graph drawing index column cell = some piece)
    {barEdge : PeriodicEdge Vertex × Nat} (barMember : barEdge ∈ graph.edges.zipIdx)
    (barCell : Cell) (line : Int) (crosses : (drawing.liftedStraightSegment barEdge.2 barCell).CrossesVerticalLine line)
    {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains (translatePolyline (Cell.scale (paddedGridSize drawing.gridSize) shift) piece.route) point)
    (barContains : GridPolyline.RealContains (paddedCrossingRoute graph drawing line (barEdge.2,barCell)) point) :
    (index,shift) = (barEdge.2,barCell) := by
  cases chord : rectangleParentChord graph drawing column (index,Cell.scale (-1) cell) with
  | none => simp [rectangleEdgePiece?,chord] at lookup
  | some keys =>
    have parents := liftedRectangleParentRoute_bar_contact_parent_eq planar degree graphLocal straight
      column (Cell.add cell shift) (index,Cell.scale (-1) cell) chord barMember barCell line crosses
      ((rectangleEdgePiece?_translated_raw_image index column cell shift lookup chord point).mp contains) barContains
    simpa [Cell.add,Cell.scale,add_assoc] using parents

end LeanTrominoes.PeriodicGridDrawing
