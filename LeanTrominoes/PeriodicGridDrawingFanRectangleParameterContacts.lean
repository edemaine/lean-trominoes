/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRectangleCutParameterRecovery
import LeanTrominoes.PeriodicGridDrawingFanPieceEndpointData
import LeanTrominoes.PeriodicGridDrawingRectangleFanOuterContacts

/-! # Equal new fan and rectangle endpoints have equal original parameters -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement

theorem fan_rectangle_endpoint_parameters_eq {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (column : Nat) (cell : Cell) {piece : EdgeRoutePiece}
    (lookup : rectangleEdgePiece? graph drawing tagged.2 column cell = some piece)
    (nonvertical : (drawing.liftedStraightSegment tagged.2 (0,0)).start.1 ≠
      (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1) (rectangleExit target : Bool)
    (sameEndpoint : (if rectangleExit then piece.route.getLast? else piece.route.head?) =
      (if target then (targetEdgePiece graph drawing tagged).route.head? else (sourceEdgePiece graph drawing tagged).route.getLast?)) :
    (if rectangleExit then piece.finish else piece.start) =
      (if target then (targetEdgePiece graph drawing tagged).start else (sourceEdgePiece graph drawing tagged).finish) := by
  obtain ⟨key,valid,_,endpoint,oldPoint⟩ := rectangleEdgePiece?_endpoint_data planar graphLocal straight tagged.2 column cell lookup rectangleExit
  have fan := fanEdgePiece_outer_endpoint_data planar degree straight member nonvertical target
  let line := if target then (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1 else (drawing.liftedStraightSegment tagged.2 (0,0)).start.1
  let right := if (drawing.liftedStraightSegment tagged.2 (0,0)).start.1 < (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1 then target else !target
  have positions := congrArg (Option.map Prod.fst) (endpoint.symm.trans sameEndpoint)
  rw [Option.map_some,fan.1] at positions
  have onCut : (rectangleLiftedPortPoint graph drawing column cell key).1 =
      (paddedRefinementFactor drawing.gridSize : Int)*line+(if right then -5 else 5)*crossingBound drawing.gridSize := Option.some.inj positions
  have rectangleParameter := rectanglePort_new_cut_recovers_parameter planar degree graphLocal straight tagged.2 column cell line right _ valid oldPoint onCut nonvertical
  have fanParameter := congrArg (drawing.liftedStraightSegment tagged.2 (0,0)).rationalXParameter fan.2
  have recovered := (GridSegment.rationalXParameter_xAtParameter nonvertical
    (if target then (targetEdgePiece graph drawing tagged).start else (sourceEdgePiece graph drawing tagged).finish)).symm.trans fanParameter
  exact rectangleParameter.trans recovered.symm

end LeanTrominoes.PeriodicGridDrawing
