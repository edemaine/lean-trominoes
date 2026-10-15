/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingRectangleCutPortParents
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingRectanglePieceEndpointData
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingLiftedCrossingPortPoints
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingCutPieceParameterPoints

/-! # Computed crossing bars join computed rectangle pieces at either end -/
namespace LeanTrominoes.PeriodicGridDrawing

theorem crossing_rectangle_piece_endpoint_join {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (index column : Nat) (cell : Cell) (line : Int) {piece : EdgeRoutePiece}
    (lookup : rectangleEdgePiece? graph drawing index column cell = some piece)
    (crosses : (drawing.liftedStraightSegment index (0,0)).CrossesVerticalLine line) (exit : Bool)
    (boundary : (if exit then piece.finish else piece.start) =
      (if exit then (crossingEdgePiece graph drawing index line).start else (crossingEdgePiece graph drawing index line).finish)) :
    (if exit then piece.route.getLast? else piece.route.head?) =
      (if exit then (crossingEdgePiece graph drawing index line).route.head? else (crossingEdgePiece graph drawing index line).route.getLast?) := by
  obtain ⟨key,valid,parent,endpoint,oldPoint⟩ := rectangleEdgePiece?_endpoint_data planar graphLocal straight index column cell lookup exit
  have nonvertical : (drawing.liftedStraightSegment index (0,0)).start.1 ≠
      (drawing.liftedStraightSegment index (0,0)).finish.1 := by rcases crosses with forward | backward <;> omega
  let right := if (drawing.liftedStraightSegment index (0,0)).start.1 < (drawing.liftedStraightSegment index (0,0)).finish.1 then exit else !exit
  have oldX := congrArg Prod.fst oldPoint
  rw [boundary] at oldX
  have crossingX := crossingEdgePiece_endpoint_original_x planar straight index line nonvertical
  have onCut : (rectanglePortOriginalPoint graph drawing column cell key).1 =
      (line : ℚ)+(if right then -columnPerturbation graph drawing else columnPerturbation graph drawing) := by
    cases exit <;> by_cases forward : (drawing.liftedStraightSegment index (0,0)).start.1 < (drawing.liftedStraightSegment index (0,0)).finish.1
    all_goals simp only [Bool.false_eq_true,if_false,if_true,right,Bool.not_false,Bool.not_true] at oldX ⊢
    all_goals simp [forward] at oldX ⊢
    · exact oldX.symm.trans (by simpa only [if_pos forward] using crossingX.2)
    · exact oldX.symm.trans (by simpa only [if_neg forward] using crossingX.2)
    · exact oldX.symm.trans (by simpa only [if_pos forward] using crossingX.1)
    · exact oldX.symm.trans (by simpa only [if_neg forward] using crossingX.1)
  obtain ⟨keyEq,lineEq⟩ := rectanglePort_crossing_of_proper_cut planar graphLocal straight index column cell line right valid parent onCut crosses
  have castLine : line = ((column+if right then 1 else 0 : Nat) : Int)+(drawing.gridSize : Int)*cell.1 := by
    have castAdd : ((column+if right then 1 else 0 : Nat) : Int) = (column : Int)+(if right then 1 else 0) := by
      split_ifs <;> simp
    rw [castAdd]
    exact lineEq
  rw [keyEq] at endpoint
  have matching := paddedCrossingRoute_lifted_boundary_port graph drawing index column cell right
  rw [← castLine] at matching
  rw [endpoint]
  symm
  cases exit <;> by_cases forward : (drawing.liftedStraightSegment index (0,0)).start.1 < (drawing.liftedStraightSegment index (0,0)).finish.1
  all_goals simpa [right,forward,crossingEdgePiece,List.head?_reverse,List.getLast?_reverse] using matching

theorem crossingEdgePiece_join_rectangle {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (index : Nat) (line : Int) {piece : EdgeRoutePiece}
    (member : piece ∈ rectangleEdgePieces graph drawing index)
    (crosses : (drawing.liftedStraightSegment index (0,0)).CrossesVerticalLine line)
    (boundary : (crossingEdgePiece graph drawing index line).finish = piece.start) :
    (crossingEdgePiece graph drawing index line).route.getLast? = piece.route.head? := by
  obtain ⟨column,_,member⟩ := List.mem_flatMap.mp member
  obtain ⟨cell,_,lookup⟩ := List.mem_filterMap.mp member
  exact (crossing_rectangle_piece_endpoint_join planar graphLocal straight index column cell line lookup crosses false boundary.symm).symm

theorem rectangle_join_crossingEdgePiece {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (index : Nat) (line : Int) {piece : EdgeRoutePiece}
    (member : piece ∈ rectangleEdgePieces graph drawing index)
    (crosses : (drawing.liftedStraightSegment index (0,0)).CrossesVerticalLine line)
    (boundary : piece.finish = (crossingEdgePiece graph drawing index line).start) :
    piece.route.getLast? = (crossingEdgePiece graph drawing index line).route.head? := by
  obtain ⟨column,_,member⟩ := List.mem_flatMap.mp member
  obtain ⟨cell,_,lookup⟩ := List.mem_filterMap.mp member
  exact crossing_rectangle_piece_endpoint_join planar graphLocal straight index column cell line lookup crosses true boundary

end LeanTrominoes.PeriodicGridDrawing
