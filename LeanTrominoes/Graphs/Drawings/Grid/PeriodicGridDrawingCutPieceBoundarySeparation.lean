/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingCutPieceParameterPoints
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingEdgePieceIntervalSeparation

/-! # Distinct cut pieces cannot be consecutive without an intervening rectangle -/
namespace LeanTrominoes.PeriodicGridDrawing
open RationalIntegerStripCover

theorem cutPiece_endpoint_location {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (tagged : PeriodicEdge Vertex × Nat)
    (nonvertical : (drawing.liftedStraightSegment tagged.2 (0,0)).start.1 ≠
      (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1) {piece : EdgeRoutePiece}
    (member : piece = sourceEdgePiece graph drawing tagged ∨
      piece ∈ crossingEdgePieces graph drawing tagged.2 ∨ piece = targetEdgePiece graph drawing tagged) :
    ∃ line : Int,
      CutContains (columnPerturbation graph drawing) line
        ((drawing.liftedStraightSegment tagged.2 (0,0)).rationalPointAtParameter piece.start).1 ∧
      CutContains (columnPerturbation graph drawing) line
        ((drawing.liftedStraightSegment tagged.2 (0,0)).rationalPointAtParameter piece.finish).1 ∧
      piece = cutEdgePiece graph drawing tagged line := by
  have positive := columnPerturbation_positive planar straight
  rcases member with source | crossing | target
  · subst piece
    refine ⟨(drawing.liftedStraightSegment tagged.2 (0,0)).start.1,?_,?_,by simp [cutEdgePiece]⟩
    · simp [sourceEdgePiece,GridSegment.rationalPointAtParameter,GridSegment.rationalXAtParameter,CutContains,positive.le]
    · rw [sourceEdgePiece_finish_original_x graph drawing tagged nonvertical]
      unfold CutContains
      split_ifs <;> constructor <;> linarith
  · obtain ⟨line,_,lookup⟩ := List.mem_filterMap.mp crossing
    split_ifs at lookup with crosses
    have pieceEq := Option.some.inj lookup
    subst piece
    have coordinates := crossingEdgePiece_endpoint_original_x planar straight tagged.2 line nonvertical
    have sourceDifferent : line ≠ (drawing.liftedStraightSegment tagged.2 (0,0)).start.1 := by rcases crosses with forward | backward <;> omega
    have targetDifferent : line ≠ (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1 := by rcases crosses with forward | backward <;> omega
    refine ⟨line,?_,?_,by simp [cutEdgePiece,sourceDifferent,targetDifferent]⟩
    · rw [coordinates.1]
      unfold CutContains
      split_ifs <;> constructor <;> linarith
    · rw [coordinates.2]
      unfold CutContains
      split_ifs <;> constructor <;> linarith
  · subst piece
    refine ⟨(drawing.liftedStraightSegment tagged.2 (0,0)).finish.1,?_,?_,by simp [cutEdgePiece,nonvertical.symm]⟩
    · rw [targetEdgePiece_start_original_x graph drawing tagged nonvertical]
      unfold CutContains
      split_ifs <;> constructor <;> linarith
    · simp only [targetEdgePiece,GridSegment.rationalPointAtParameter,GridSegment.rationalXAtParameter]
      unfold CutContains
      constructor <;> linarith

theorem cutPieces_cannot_join {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (tagged : PeriodicEdge Vertex × Nat)
    (nonvertical : (drawing.liftedStraightSegment tagged.2 (0,0)).start.1 ≠
      (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1) {first last : EdgeRoutePiece}
    (firstMember : first = sourceEdgePiece graph drawing tagged ∨
      first ∈ crossingEdgePieces graph drawing tagged.2 ∨ first = targetEdgePiece graph drawing tagged)
    (lastMember : last = sourceEdgePiece graph drawing tagged ∨
      last ∈ crossingEdgePieces graph drawing tagged.2 ∨ last = targetEdgePiece graph drawing tagged)
    (positive : first.start < first.finish) (boundary : first.finish = last.start) : False := by
  obtain ⟨firstLine,_,firstCut,firstEq⟩ := cutPiece_endpoint_location planar straight tagged nonvertical firstMember
  obtain ⟨lastLine,lastCut,_,lastEq⟩ := cutPiece_endpoint_location planar straight tagged nonvertical lastMember
  rw [← boundary] at lastCut
  have small := (columnPerturbation_le_cutMargin planar straight).trans_lt (columnCutMargin_lt_half graph drawing)
  have lines := cut_line_unique small firstCut lastCut
  have pieces : first = last := firstEq.trans (by simpa only [lines] using lastEq.symm)
  rw [← pieces] at boundary
  linarith

end LeanTrominoes.PeriodicGridDrawing
