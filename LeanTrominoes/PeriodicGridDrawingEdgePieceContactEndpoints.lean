/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRectanglePieceContactEndpoints
import LeanTrominoes.PeriodicGridDrawingEdgePieceJoins

/-! # Distinct computed pieces of a nonvertical edge can meet only at their endpoints -/
namespace LeanTrominoes.PeriodicGridDrawing
open PeriodicOrthocrossing

theorem rectangle_cut_piece_contact_endpoints {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    {rectangle cut : EdgeRoutePiece} (rectangleMember : rectangle ∈ rectangleEdgePieces graph drawing tagged.2)
    (cutMember : cut = sourceEdgePiece graph drawing tagged ∨
      cut ∈ crossingEdgePieces graph drawing tagged.2 ∨ cut = targetEdgePiece graph drawing tagged)
    {point : ℝ × ℝ} (rectangleContains : GridPolyline.RealContains rectangle.route point)
    (cutContains : GridPolyline.RealContains cut.route point) :
    GridPolyline.RealIsEndpoint rectangle.route point ∧ GridPolyline.RealIsEndpoint cut.route point := by
  obtain ⟨column,_,rectangleMember⟩ := List.mem_flatMap.mp rectangleMember
  obtain ⟨cell,_,lookup⟩ := List.mem_filterMap.mp rectangleMember
  rcases cutMember with source | crossing | target
  · subst cut
    have contact := rectangleEdgePiece?_fan_contact_endpoints planar degree graphLocal straight tagged.2 column cell lookup
      (sourcePort_mem_allPorts graph member) (0,0) rectangleContains
      ((sourceEdgePiece_lifted_image graph drawing tagged point).mp cutContains)
    refine ⟨contact.1,?_⟩
    rw [liftedPaddedIncidenceRoute_eq_translate] at contact
    simpa [sourceEdgePiece,Cell.scale,translatePolyline_zero] using contact.2
  · obtain ⟨line,_,lookup⟩ := List.mem_filterMap.mp crossing
    split_ifs at lookup with crosses
    have equal := Option.some.inj lookup
    subst cut
    exact rectangleEdgePiece?_crossing_contact_endpoints planar degree graphLocal straight tagged.2 column cell ‹_› line rectangleContains cutContains
  · subst cut
    have raw : GridPolyline.RealContains (liftedPaddedIncidenceRoute graph drawing (targetPort tagged.1 tagged.2) tagged.1.offset) point :=
      (GridPolyline.realContains_reverse _ _).mp cutContains
    have contact := rectangleEdgePiece?_fan_contact_endpoints planar degree graphLocal straight tagged.2 column cell lookup
      (targetPort_mem_allPorts graph member) tagged.1.offset rectangleContains raw
    exact ⟨contact.1,(GridPolyline.realIsEndpoint_reverse _ _).mpr contact.2⟩

theorem nonverticalEdgePieces_distinct_contact_endpoints {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (nonvertical : (drawing.liftedStraightSegment tagged.2 (0,0)).start.1 ≠
      (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1) {first last : EdgeRoutePiece}
    (firstMember : first ∈ nonverticalEdgePieces graph drawing tagged)
    (lastMember : last ∈ nonverticalEdgePieces graph drawing tagged) (different : first ≠ last)
    {point : ℝ × ℝ} (firstContains : GridPolyline.RealContains first.route point)
    (lastContains : GridPolyline.RealContains last.route point) :
    GridPolyline.RealIsEndpoint first.route point ∧ GridPolyline.RealIsEndpoint last.route point := by
  have classify : ∀ piece ∈ nonverticalEdgePieces graph drawing tagged,
      piece ∈ rectangleEdgePieces graph drawing tagged.2 ∨
        (piece = sourceEdgePiece graph drawing tagged ∨ piece ∈ crossingEdgePieces graph drawing tagged.2 ∨ piece = targetEdgePiece graph drawing tagged) := by
    intro piece pieceMember
    simp only [nonverticalEdgePieces,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at pieceMember
    tauto
  rcases classify first firstMember with firstRectangle | firstCut
  · rcases classify last lastMember with lastRectangle | lastCut
    · exact rectangleEdgePieces_distinct_contact_endpoints planar degree graphLocal straight tagged.2 firstRectangle lastRectangle different firstContains lastContains
    · exact rectangle_cut_piece_contact_endpoints planar degree graphLocal straight member firstRectangle lastCut firstContains lastContains
  · rcases classify last lastMember with lastRectangle | lastCut
    · exact (rectangle_cut_piece_contact_endpoints planar degree graphLocal straight member lastRectangle firstCut lastContains firstContains).symm
    · exact (different (cutPieces_contact_eq planar degree graphLocal straight member nonvertical firstCut lastCut firstContains lastContains)).elim

end LeanTrominoes.PeriodicGridDrawing
