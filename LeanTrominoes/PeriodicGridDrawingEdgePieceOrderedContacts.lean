/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRectangleParameterContacts
import LeanTrominoes.PeriodicGridDrawingCrossingRectangleParameterContacts
import LeanTrominoes.PeriodicGridDrawingFanRectangleContactParameters
import LeanTrominoes.GridPolylineOrderedEndpointContacts

/-! # Ordered computed pieces can meet only at their common consecutive parameter -/
namespace LeanTrominoes.PeriodicGridDrawing

theorem nonverticalEdgePieces_ordered_contact {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (nonvertical : (drawing.liftedStraightSegment tagged.2 (0,0)).start.1 ≠
      (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1) {first last : EdgeRoutePiece}
    (firstMember : first ∈ nonverticalEdgePieces graph drawing tagged)
    (lastMember : last ∈ nonverticalEdgePieces graph drawing tagged)
    (ordered : first.finish ≤ last.start) {point : ℝ × ℝ}
    (firstContains : GridPolyline.RealContains first.route point)
    (lastContains : GridPolyline.RealContains last.route point) :
    first.finish = last.start ∧ point = realCell (first.route.getLast?.getD (0,0)) := by
  have firstBounds := nonverticalEdgePieces_interval_bounds planar degree graphLocal straight tagged nonvertical firstMember
  have lastBounds := nonverticalEdgePieces_interval_bounds planar degree graphLocal straight tagged nonvertical lastMember
  have different : first ≠ last := by intro equal; rw [equal] at firstBounds ordered; linarith [firstBounds.2.1]
  have endpoints := nonverticalEdgePieces_distinct_contact_endpoints planar degree graphLocal straight member nonvertical firstMember lastMember different firstContains lastContains
  have classify : ∀ piece ∈ nonverticalEdgePieces graph drawing tagged,
      piece ∈ rectangleEdgePieces graph drawing tagged.2 ∨
        (piece = sourceEdgePiece graph drawing tagged ∨ piece ∈ crossingEdgePieces graph drawing tagged.2 ∨ piece = targetEdgePiece graph drawing tagged) := by
    intro piece pieceMember
    simp only [nonverticalEdgePieces,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at pieceMember
    tauto
  rcases classify first firstMember with firstRectangle | firstCut
  · obtain ⟨firstColumn,firstColumnMember,firstPieceMember⟩ := List.mem_flatMap.mp firstRectangle
    obtain ⟨firstCell,_,firstLookup⟩ := List.mem_filterMap.mp firstPieceMember
    rcases classify last lastMember with lastRectangle | lastCut
    · obtain ⟨lastColumn,lastColumnMember,lastPieceMember⟩ := List.mem_flatMap.mp lastRectangle
      obtain ⟨lastCell,_,lastLookup⟩ := List.mem_filterMap.mp lastPieceMember
      have indicesDifferent : (firstColumn,firstCell) ≠ (lastColumn,lastCell) := by
        intro equal
        have columns := congrArg Prod.fst equal
        have cells := congrArg Prod.snd equal
        change firstColumn = lastColumn at columns
        change firstCell = lastCell at cells
        rw [columns,cells] at firstLookup
        exact different (Option.some.inj (firstLookup.symm.trans lastLookup))
      exact GridPolyline.ordered_endpoint_contact firstBounds.2.1 lastBounds.2.1 ordered
        (rectangle_rectangle_endpoint_parameters_eq planar degree graphLocal straight tagged.2 firstColumn lastColumn
          (List.mem_range.mp firstColumnMember) (List.mem_range.mp lastColumnMember) firstCell lastCell firstLookup lastLookup indicesDifferent)
        endpoints.1 endpoints.2
    · rcases lastCut with source | crossing | target
      · subst last
        change first.finish ≤ 0 at ordered
        linarith [firstBounds.1,firstBounds.2.1]
      · obtain ⟨line,_,lookup⟩ := List.mem_filterMap.mp crossing
        split_ifs at lookup with crosses
        have equal := Option.some.inj lookup
        subst last
        exact GridPolyline.ordered_endpoint_contact firstBounds.2.1 lastBounds.2.1 ordered
          (crossing_rectangle_endpoint_parameters_eq planar degree graphLocal straight tagged.2 firstColumn firstCell line firstLookup nonvertical)
          endpoints.1 endpoints.2
      · subst last
        obtain ⟨⟨rectangleExit,parameters,atRectangle⟩,_⟩ := rectangle_fan_contact_parameter planar degree graphLocal straight member
          firstColumn firstCell firstLookup nonvertical true firstContains lastContains
        cases rectangleExit
        · simp only [Bool.false_eq_true,if_false,if_true] at parameters
          linarith [firstBounds.2.1]
        · exact ⟨parameters,atRectangle⟩
  · rcases classify last lastMember with lastRectangle | lastCut
    · obtain ⟨lastColumn,_,lastPieceMember⟩ := List.mem_flatMap.mp lastRectangle
      obtain ⟨lastCell,_,lastLookup⟩ := List.mem_filterMap.mp lastPieceMember
      rcases firstCut with source | crossing | target
      · subst first
        obtain ⟨⟨rectangleExit,parameters,_⟩,atFan⟩ := rectangle_fan_contact_parameter planar degree graphLocal straight member
          lastColumn lastCell lastLookup nonvertical false lastContains firstContains
        cases rectangleExit
        · exact ⟨parameters.symm,atFan⟩
        · simp only [Bool.false_eq_true,if_false,if_true] at parameters
          linarith [lastBounds.2.1]
      · obtain ⟨line,_,lookup⟩ := List.mem_filterMap.mp crossing
        split_ifs at lookup with crosses
        have equal := Option.some.inj lookup
        subst first
        exact GridPolyline.ordered_endpoint_contact firstBounds.2.1 lastBounds.2.1 ordered
          (fun firstExit lastExit equal => (crossing_rectangle_endpoint_parameters_eq planar degree graphLocal straight tagged.2 lastColumn lastCell line lastLookup nonvertical lastExit firstExit equal.symm).symm)
          endpoints.1 endpoints.2
      · subst first
        change 1 ≤ last.start at ordered
        linarith [lastBounds.2.1,lastBounds.2.2]
    · exact (different (cutPieces_contact_eq planar degree graphLocal straight member nonvertical firstCut lastCut firstContains lastContains)).elim

end LeanTrominoes.PeriodicGridDrawing
