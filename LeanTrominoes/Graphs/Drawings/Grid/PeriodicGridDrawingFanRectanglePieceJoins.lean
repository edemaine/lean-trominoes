/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingRectangleCutPortParents
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingRectanglePieceEndpointData
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingLiftedCrossingPortPoints
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingCutPieceParameterPoints
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingEdgePieceEndpoints

/-! # Computed source and target fans join their computed rectangle pieces -/
namespace LeanTrominoes.PeriodicGridDrawing
open GeneralVertexNormalization PeriodicOrthocrossing

theorem fan_rectangle_piece_endpoint_join {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (column : Nat) (cell : Cell) {piece : EdgeRoutePiece}
    (lookup : rectangleEdgePiece? graph drawing tagged.2 column cell = some piece)
    (nonvertical : (drawing.liftedStraightSegment tagged.2 (0,0)).start.1 ≠
      (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1) (target : Bool)
    (boundary : (if target then piece.finish else piece.start) =
      (if target then (targetEdgePiece graph drawing tagged).start else (sourceEdgePiece graph drawing tagged).finish)) :
    (if target then piece.route.getLast? else piece.route.head?) =
      (if target then (targetEdgePiece graph drawing tagged).route.head? else (sourceEdgePiece graph drawing tagged).route.getLast?) := by
  obtain ⟨key,valid,parent,endpoint,oldPoint⟩ := rectangleEdgePiece?_endpoint_data planar graphLocal straight tagged.2 column cell lookup target
  let right := if (drawing.liftedStraightSegment tagged.2 (0,0)).start.1 < (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1 then target else !target
  have oldX := congrArg Prod.fst oldPoint
  rw [boundary] at oldX
  have sourceX := sourceEdgePiece_finish_original_x graph drawing tagged nonvertical
  have targetX := targetEdgePiece_start_original_x graph drawing tagged nonvertical
  have onCut : (rectanglePortOriginalPoint graph drawing column cell key).1 =
      (if target then (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1
        else (drawing.liftedStraightSegment tagged.2 (0,0)).start.1 : Int)+
        (if right then -columnPerturbation graph drawing else columnPerturbation graph drawing) := by
    cases target <;> by_cases forward : (drawing.liftedStraightSegment tagged.2 (0,0)).start.1 < (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1
    all_goals simp [right,forward] at oldX ⊢
    · exact oldX.symm.trans (by simpa only [if_pos forward] using sourceX)
    · exact oldX.symm.trans (by simpa only [if_neg forward] using sourceX)
    · exact oldX.symm.trans (by simpa only [if_pos forward] using targetX)
    · exact oldX.symm.trans (by simpa only [if_neg forward] using targetX)
  obtain ⟨keyEq,cellEq⟩ := rectanglePort_incidence_of_endpoint_cut planar graphLocal straight member column cell right target valid parent onCut nonvertical
  rw [keyEq] at valid endpoint
  have port := rectangle_incidence_port_point planar degree straight column right valid
  rw [rectangleLiftedPortPoint_eq_translate,port,cellEq] at endpoint
  rw [endpoint]
  cases target
  · simp only [Bool.false_eq_true,if_false,endpointPort,sourcePort] at *
    rw [sourceEdgePiece_last planar degree straight member]
    simp [Cell.scale,Cell.add,sourcePort]
  · simp only [if_true,endpointPort,targetPort] at *
    rw [targetEdgePiece_head planar degree straight member]
    rfl

theorem sourceEdgePiece_join_rectangle {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (nonvertical : (drawing.liftedStraightSegment tagged.2 (0,0)).start.1 ≠
      (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1) {piece : EdgeRoutePiece}
    (pieceMember : piece ∈ rectangleEdgePieces graph drawing tagged.2)
    (boundary : (sourceEdgePiece graph drawing tagged).finish = piece.start) :
    (sourceEdgePiece graph drawing tagged).route.getLast? = piece.route.head? := by
  obtain ⟨column,_,pieceMember⟩ := List.mem_flatMap.mp pieceMember
  obtain ⟨cell,_,lookup⟩ := List.mem_filterMap.mp pieceMember
  exact (fan_rectangle_piece_endpoint_join planar degree graphLocal straight member column cell lookup nonvertical false boundary.symm).symm

theorem rectangle_join_targetEdgePiece {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (nonvertical : (drawing.liftedStraightSegment tagged.2 (0,0)).start.1 ≠
      (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1) {piece : EdgeRoutePiece}
    (pieceMember : piece ∈ rectangleEdgePieces graph drawing tagged.2)
    (boundary : piece.finish = (targetEdgePiece graph drawing tagged).start) :
    piece.route.getLast? = (targetEdgePiece graph drawing tagged).route.head? := by
  obtain ⟨column,_,pieceMember⟩ := List.mem_flatMap.mp pieceMember
  obtain ⟨cell,_,lookup⟩ := List.mem_filterMap.mp pieceMember
  exact fan_rectangle_piece_endpoint_join planar degree graphLocal straight member column cell lookup nonvertical true boundary

end LeanTrominoes.PeriodicGridDrawing
