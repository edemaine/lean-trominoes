/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingRectanglePieceRawRoutes
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingRectangleRouteSeparation
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingRectangleTwoSidedContacts
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingCutPieceGeometricSeparation

/-! # Geometric contacts of executable rectangle pieces occur at both endpoints -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalBoundaryRouting OrthogonalDrawingRefinement PeriodicOrthocrossing

theorem rectangleEdgePiece?_raw_source {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (compatible : drawing.IsCompatible graph) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (index column : Nat) (cell : Cell) {piece : EdgeRoutePiece}
    (lookup : rectangleEdgePiece? graph drawing index column cell = some piece) :
    ∃ chord ∈ rectangleChordFamily graph drawing column, ∀ point,
      (GridPolyline.RealContains piece.route point ↔ GridPolyline.RealContains (liftedRectangleInputRoute graph drawing column cell chord) point) ∧
      (GridPolyline.RealIsEndpoint piece.route point ↔ GridPolyline.RealIsEndpoint (liftedRectangleInputRoute graph drawing column cell chord) point) := by
  cases chord : rectangleParentChord graph drawing column (index,Cell.scale (-1) cell) with
  | none => simp [rectangleEdgePiece?,chord] at lookup
  | some keys =>
    refine ⟨(keys.1.integralPort graph drawing column,keys.2.integralPort graph drawing column),
      rectangleParentChord_mem_family compatible graphLocal straight column (index,Cell.scale (-1) cell) chord,?_⟩
    intro point
    exact rectangleEdgePiece?_raw_image_endpoints index column cell lookup chord point

theorem rectangleEdgePieces_distinct_contact_endpoints {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (index : Nat) {first last : EdgeRoutePiece}
    (firstMember : first ∈ rectangleEdgePieces graph drawing index) (lastMember : last ∈ rectangleEdgePieces graph drawing index)
    (different : first ≠ last) {point : ℝ × ℝ}
    (firstContains : GridPolyline.RealContains first.route point) (lastContains : GridPolyline.RealContains last.route point) :
    GridPolyline.RealIsEndpoint first.route point ∧ GridPolyline.RealIsEndpoint last.route point := by
  obtain ⟨firstColumn,firstColumnMember,firstPieceMember⟩ := List.mem_flatMap.mp firstMember
  obtain ⟨firstCell,_,firstLookup⟩ := List.mem_filterMap.mp firstPieceMember
  obtain ⟨lastColumn,lastColumnMember,lastPieceMember⟩ := List.mem_flatMap.mp lastMember
  obtain ⟨lastCell,_,lastLookup⟩ := List.mem_filterMap.mp lastPieceMember
  have indicesDifferent : (firstColumn,firstCell) ≠ (lastColumn,lastCell) := by
    intro equal
    have columns := congrArg Prod.fst equal
    have cells := congrArg Prod.snd equal
    change firstColumn = lastColumn at columns
    change firstCell = lastCell at cells
    rw [columns,cells] at firstLookup
    exact different (Option.some.inj (firstLookup.symm.trans lastLookup))
  obtain ⟨firstChord,firstChordMember,firstImage⟩ := rectangleEdgePiece?_raw_source planar.1.1 graphLocal straight index firstColumn firstCell firstLookup
  obtain ⟨lastChord,lastChordMember,lastImage⟩ := rectangleEdgePiece?_raw_source planar.1.1 graphLocal straight index lastColumn lastCell lastLookup
  have firstRaw := (firstImage point).1.mp firstContains
  have lastRaw := (lastImage point).1.mp lastContains
  refine ⟨(firstImage point).2.mpr ?_,(lastImage point).2.mpr ?_⟩
  · exact liftedRectangleInputRoutes_distinct_cells_contact_endpoint planar degree graphLocal straight
      (List.mem_range.mp firstColumnMember) (List.mem_range.mp lastColumnMember) firstChordMember lastChordMember
      firstCell lastCell indicesDifferent firstRaw lastRaw
  · exact liftedRectangleInputRoutes_distinct_cells_contact_endpoint planar degree graphLocal straight
      (List.mem_range.mp lastColumnMember) (List.mem_range.mp firstColumnMember) lastChordMember firstChordMember
      lastCell firstCell (Ne.symm indicesDifferent) lastRaw firstRaw

theorem rectangleEdgePiece?_crossing_contact_endpoints {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (index column : Nat) (cell : Cell) {piece : EdgeRoutePiece}
    (lookup : rectangleEdgePiece? graph drawing index column cell = some piece) (line : Int) {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains piece.route point)
    (barContains : GridPolyline.RealContains (crossingEdgePiece graph drawing index line).route point) :
    GridPolyline.RealIsEndpoint piece.route point ∧ GridPolyline.RealIsEndpoint (crossingEdgePiece graph drawing index line).route point := by
  obtain ⟨chord,chordMember,image⟩ := rectangleEdgePiece?_raw_source planar.1.1 graphLocal straight index column cell lookup
  have contacts := crossing_bar_rectangle_contact_endpoints planar degree graphLocal straight chordMember cell
    ((image point).1.mp contains) line _ ((crossingEdgePiece_raw_image graph drawing index line point).mp barContains)
  refine ⟨(image point).2.mpr contacts.1,?_⟩
  unfold crossingEdgePiece
  dsimp only
  split_ifs
  · exact contacts.2
  · exact (GridPolyline.realIsEndpoint_reverse _ _).mpr contacts.2

theorem rectangleEdgePiece?_fan_contact_endpoints {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (index column : Nat) (cell : Cell) {piece : EdgeRoutePiece}
    (lookup : rectangleEdgePiece? graph drawing index column cell = some piece)
    {port : GraphPort Vertex} (portMember : port ∈ allPorts graph) (fanCell : Cell) {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains piece.route point)
    (fanContains : GridPolyline.RealContains (liftedPaddedIncidenceRoute graph drawing port fanCell) point) :
    GridPolyline.RealIsEndpoint piece.route point ∧ GridPolyline.RealIsEndpoint (liftedPaddedIncidenceRoute graph drawing port fanCell) point := by
  obtain ⟨chord,chordMember,image⟩ := rectangleEdgePiece?_raw_source planar.1.1 graphLocal straight index column cell lookup
  have distinct := distinctPortRayKeys_of_planar_straight planar straight
  have contacts := vertex_fan_rectangle_contact_endpoints planar degree graphLocal straight chordMember cell
    ((image point).1.mp contains) _ _ _ (vertexAnchorProfile_degree_le_four distinct degree _)
    (incidenceAnchorIndex_valid distinct degree portMember) fanContains
  exact ⟨(image point).2.mpr contacts.1,contacts.2⟩

end LeanTrominoes.PeriodicGridDrawing
