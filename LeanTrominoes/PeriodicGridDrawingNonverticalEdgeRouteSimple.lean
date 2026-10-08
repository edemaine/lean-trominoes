/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingEdgePieceOrderedContacts
import LeanTrominoes.GridPolylineParameterizedWordSeparation

/-! # Unconditional simplicity and orthogonality of the executable nonvertical route -/
namespace LeanTrominoes.PeriodicGridDrawing
open PeriodicOrthocrossing

theorem nonverticalEdgePieces_separated_word {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (nonvertical : (drawing.liftedStraightSegment tagged.2 (0,0)).start.1 ≠
      (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1) :
    GridPolyline.SeparatedWord ((sortEdgeRoutePieces (nonverticalEdgePieces graph drawing tagged)).map EdgeRoutePiece.route) := by
  let sorted := sortEdgeRoutePieces (nonverticalEdgePieces graph drawing tagged)
  have positive : ∀ piece ∈ sorted, piece.start < piece.finish := fun piece pieceMember =>
    (nonverticalEdgePieces_interval_bounds planar degree graphLocal straight tagged nonvertical
      (sortEdgeRoutePieces_mem_iff.mp pieceMember)).2.1
  have disjoint : ∀ first ∈ sorted, ∀ last ∈ sorted, first ≠ last → first.InteriorsDisjoint last :=
    fun first fm last lm different => nonverticalEdgePieces_interiors_disjoint planar graphLocal straight tagged nonvertical
      (sortEdgeRoutePieces_mem_iff.mp fm) (sortEdgeRoutePieces_mem_iff.mp lm) different
  have ordered := edgeRoutePieces_finish_order sorted (sortEdgeRoutePieces_nodup _) positive (sortEdgeRoutePieces_start_order _) disjoint
  exact GridPolyline.separatedWord_of_parameter_order sorted EdgeRoutePiece.route EdgeRoutePiece.start EdgeRoutePiece.finish positive ordered
    (fun first fm last lm before point firstContains lastContains =>
      nonverticalEdgePieces_ordered_contact planar degree graphLocal straight member nonvertical
        (sortEdgeRoutePieces_mem_iff.mp fm) (sortEdgeRoutePieces_mem_iff.mp lm) before firstContains lastContains)

theorem nonverticalEdgeRoute_valid {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (nonvertical : (drawing.liftedStraightSegment tagged.2 (0,0)).start.1 ≠
      (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1) :
    GridPolyline.IsRealOpenSimple (nonverticalEdgeRoute graph drawing tagged) ∧
      OrthogonalPolyline (nonverticalEdgeRoute graph drawing tagged) ∧
      ∀ point, GridPolyline.RealContains (nonverticalEdgeRoute graph drawing tagged) point ↔
        ∃ piece ∈ nonverticalEdgePieces graph drawing tagged, GridPolyline.RealContains piece.route point :=
  nonverticalEdgeRoute_valid_of_separated planar degree graphLocal straight member nonvertical
    (nonverticalEdgePieces_separated_word planar degree graphLocal straight member nonvertical)

end LeanTrominoes.PeriodicGridDrawing
