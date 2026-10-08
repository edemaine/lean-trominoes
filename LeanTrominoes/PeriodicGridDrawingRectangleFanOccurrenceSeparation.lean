/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRectangleStripContactKeys
import LeanTrominoes.PeriodicGridDrawingRectanglePortPhysicalPieces
import LeanTrominoes.PeriodicGridDrawingVerticalRectangleSeparation
import LeanTrominoes.PeriodicGridDrawingRectanglePieceOccurrenceSeparation

/-! # A rectangle touching a vertex fan identifies the fan's edge-end occurrence -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement PeriodicOrthocrossing GeneralVertexNormalization

theorem liftedRectangleParentRoute_fan_contact_parent_eq {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (column : Nat) (cell : Cell) (parent : Nat × Cell)
    {keys : RectanglePortKey Vertex × RectanglePortKey Vertex}
    (lookup : rectangleParentChord graph drawing column parent = some keys)
    {port : GraphPort Vertex} (portMember : port ∈ allPorts graph) (fanCell : Cell)
    {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains (liftedRectangleInputRoute graph drawing column cell
      (keys.1.integralPort graph drawing column,keys.2.integralPort graph drawing column)) point)
    (fanContains : GridPolyline.RealContains (liftedPaddedIncidenceRoute graph drawing port fanCell) point) :
    ∃ tagged ∈ graph.edges.zipIdx, ∃ target, endpointPort tagged target = port ∧
      (parent.1,Cell.add parent.2 cell) = (tagged.2,Cell.add (endpointCell tagged target) fanCell) := by
  obtain ⟨right,raw,valid,keyParent,pointEq,_⟩ := liftedRectangleParentRoute_strip_contact_key
    planar degree graphLocal straight column cell parent lookup contains
    (Cell.add (drawing.vertexPosition graph port.vertex) (drawing.periodTranslation fanCell)).1
    (enlargedRectangleTemplate_real_bounds _ _ _ _ _ fanContains).1
  cases raw with
  | crossing key =>
    have onBar := rectangle_crossing_port_on_bar graph drawing column cell right key
    rw [← pointEq] at onBar
    obtain ⟨tagged,taggedMember,indexEq⟩ := rectanglePort_parent_tagged valid
    change tagged.2 = key.1 at indexEq
    have crosses := rectangle_crossing_port_lifted_crosses column cell right valid
    rw [← indexEq] at crosses
    have crossing := periodic_crossing_residue_mem planar.1.1 taggedMember (straight _ taggedMember)
      (graphLocal _ (List.fst_mem_of_mem_zipIdx taggedMember)) (Cell.add key.2 cell) crosses
    rw [indexEq] at crossing
    exact (paddedCrossingBar_avoids_incidence_route planar.1.1 degree crossing portMember fanCell onBar fanContains).elim
  | incidence tagged target =>
    have onFan := rectangle_incidence_port_on_fan planar degree straight column cell right valid
    rw [← pointEq] at onFan
    have contact := liftedPaddedIncidenceRoutes_contact planar.1.1 (distinctPortRayKeys_of_planar_straight planar straight)
      degree (endpointPort_mem graph valid.1 target) portMember cell fanCell onFan fanContains
    have portEq : endpointPort tagged target = port := by
      rcases contact.2.2 with equal | center
      · exact equal
      · have chordMember := rectangleParentChord_mem_family planar.1.1 graphLocal straight column parent lookup
        have x := congrArg Prod.fst center
        simp only [realCell,Cell.scale,Int.cast_mul,Int.cast_natCast] at x
        exact (liftedRectangleInputRoute_avoids_scaled_column planar degree graphLocal straight chordMember cell _ contains x).elim
    refine ⟨tagged,valid.1,target,portEq,?_⟩
    rw [← keyParent,contact.2.1]
    rfl

theorem rectangleEdgePiece_fan_contact_occurrence_eq {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (index column : Nat) (cell shift : Cell) {piece : EdgeRoutePiece}
    (lookup : rectangleEdgePiece? graph drawing index column cell = some piece)
    {port : GraphPort Vertex} (portMember : port ∈ allPorts graph) (fanCell : Cell)
    {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains (translatePolyline (Cell.scale (paddedGridSize drawing.gridSize) shift) piece.route) point)
    (fanContains : GridPolyline.RealContains (liftedPaddedIncidenceRoute graph drawing port fanCell) point) :
    ∃ tagged ∈ graph.edges.zipIdx, ∃ target, endpointPort tagged target = port ∧
      (index,shift) = (tagged.2,Cell.add (endpointCell tagged target) fanCell) := by
  cases chord : rectangleParentChord graph drawing column (index,Cell.scale (-1) cell) with
  | none => simp [rectangleEdgePiece?,chord] at lookup
  | some keys =>
    obtain ⟨tagged,taggedMember,target,portEq,parents⟩ := liftedRectangleParentRoute_fan_contact_parent_eq
      planar degree graphLocal straight column (Cell.add cell shift) (index,Cell.scale (-1) cell) chord portMember fanCell
      ((rectangleEdgePiece?_translated_raw_image index column cell shift lookup chord point).mp contains) fanContains
    exact ⟨tagged,taggedMember,target,portEq,by simpa [Cell.add,Cell.scale,add_assoc] using parents⟩

end LeanTrominoes.PeriodicGridDrawing
