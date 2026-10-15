/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingRectanglePieceJoins
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingCrossingRectanglePieceJoins
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingFanRectanglePieceJoins
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingCutPieceBoundarySeparation
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingEdgeRouteAssembly

/-! # All consecutive computed pieces of a nonvertical edge join -/
namespace LeanTrominoes.PeriodicGridDrawing
open PeriodicOrthocrossing

theorem nonverticalEdgePieces_join {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (nonvertical : (drawing.liftedStraightSegment tagged.2 (0,0)).start.1 ≠
      (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1) {first last : EdgeRoutePiece}
    (firstMember : first ∈ nonverticalEdgePieces graph drawing tagged)
    (lastMember : last ∈ nonverticalEdgePieces graph drawing tagged)
    (boundary : first.finish = last.start) : first.route.getLast? = last.route.head? := by
  have firstBounds := nonverticalEdgePieces_interval_bounds planar degree graphLocal straight tagged nonvertical firstMember
  have lastBounds := nonverticalEdgePieces_interval_bounds planar degree graphLocal straight tagged nonvertical lastMember
  have classify : ∀ piece ∈ nonverticalEdgePieces graph drawing tagged,
      piece ∈ rectangleEdgePieces graph drawing tagged.2 ∨
        (piece = sourceEdgePiece graph drawing tagged ∨ piece ∈ crossingEdgePieces graph drawing tagged.2 ∨ piece = targetEdgePiece graph drawing tagged) := by
    intro piece pieceMember
    simp only [nonverticalEdgePieces,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at pieceMember
    tauto
  rcases classify first firstMember with firstRectangle | firstCut
  · rcases classify last lastMember with lastRectangle | lastCut
    · exact rectangleEdgePieces_join planar degree graphLocal straight tagged.2 firstRectangle lastRectangle boundary
    · rcases lastCut with source | crossing | target
      · subst last
        change first.finish = 0 at boundary
        linarith [firstBounds.1,firstBounds.2.1]
      · obtain ⟨line,_,lookup⟩ := List.mem_filterMap.mp crossing
        split_ifs at lookup with crosses
        have equal := Option.some.inj lookup
        subst last
        exact rectangle_join_crossingEdgePiece planar graphLocal straight tagged.2 line firstRectangle crosses boundary
      · subst last
        exact rectangle_join_targetEdgePiece planar degree graphLocal straight member nonvertical firstRectangle boundary
  · rcases classify last lastMember with lastRectangle | lastCut
    · rcases firstCut with source | crossing | target
      · subst first
        exact sourceEdgePiece_join_rectangle planar degree graphLocal straight member nonvertical lastRectangle boundary
      · obtain ⟨line,_,lookup⟩ := List.mem_filterMap.mp crossing
        split_ifs at lookup with crosses
        have equal := Option.some.inj lookup
        subst first
        exact crossingEdgePiece_join_rectangle planar graphLocal straight tagged.2 line lastRectangle crosses boundary
      · subst first
        change 1 = last.start at boundary
        linarith [lastBounds.2.1,lastBounds.2.2]
    · exact (cutPieces_cannot_join planar straight tagged nonvertical firstCut lastCut firstBounds.2.1 boundary).elim

theorem nonverticalEdgeRoute_valid_of_separated {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (nonvertical : (drawing.liftedStraightSegment tagged.2 (0,0)).start.1 ≠
      (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1)
    (separated : GridPolyline.SeparatedWord ((sortEdgeRoutePieces (nonverticalEdgePieces graph drawing tagged)).map EdgeRoutePiece.route)) :
    GridPolyline.IsRealOpenSimple (nonverticalEdgeRoute graph drawing tagged) ∧
      OrthogonalPolyline (nonverticalEdgeRoute graph drawing tagged) ∧
      ∀ point, GridPolyline.RealContains (nonverticalEdgeRoute graph drawing tagged) point ↔
        ∃ piece ∈ nonverticalEdgePieces graph drawing tagged, GridPolyline.RealContains piece.route point :=
  nonverticalEdgeRoute_valid_of_joins planar degree graphLocal straight member nonvertical
    (fun _ fm _ lm => nonverticalEdgePieces_join planar degree graphLocal straight member nonvertical fm lm) separated

end LeanTrominoes.PeriodicGridDrawing
