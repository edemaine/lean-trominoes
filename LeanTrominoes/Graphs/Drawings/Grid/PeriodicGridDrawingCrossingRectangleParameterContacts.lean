/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingRectangleCutParameterRecovery
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingCrossingPieceEndpointData
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingRectanglePieceContactEndpoints

/-! # Equal new crossing and rectangle endpoints have equal original parameters -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement

theorem crossing_rectangle_endpoint_parameters_eq {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (index column : Nat) (cell : Cell) (line : Int) {piece : EdgeRoutePiece}
    (lookup : rectangleEdgePiece? graph drawing index column cell = some piece)
    (nonvertical : (drawing.liftedStraightSegment index (0,0)).start.1 ≠
      (drawing.liftedStraightSegment index (0,0)).finish.1) (rectangleExit crossingExit : Bool)
    (sameEndpoint : (if rectangleExit then piece.route.getLast? else piece.route.head?) =
      (if crossingExit then (crossingEdgePiece graph drawing index line).route.getLast? else (crossingEdgePiece graph drawing index line).route.head?)) :
    (if rectangleExit then piece.finish else piece.start) =
      (if crossingExit then (crossingEdgePiece graph drawing index line).finish else (crossingEdgePiece graph drawing index line).start) := by
  obtain ⟨key,valid,_,endpoint,oldPoint⟩ := rectangleEdgePiece?_endpoint_data planar graphLocal straight index column cell lookup rectangleExit
  have crossing := crossingEdgePiece_endpoint_data planar straight index line nonvertical crossingExit
  let right := if (drawing.liftedStraightSegment index (0,0)).start.1 < (drawing.liftedStraightSegment index (0,0)).finish.1 then !crossingExit else crossingExit
  have positions := Option.some.inj (endpoint.symm.trans (sameEndpoint.trans crossing.1))
  have onCut : (rectangleLiftedPortPoint graph drawing column cell key).1 =
      (paddedRefinementFactor drawing.gridSize : Int)*line+(if right then -5 else 5)*crossingBound drawing.gridSize :=
    congrArg Prod.fst positions
  have rectangleParameter := rectanglePort_new_cut_recovers_parameter planar degree graphLocal straight index column cell line right _ valid oldPoint onCut nonvertical
  have crossingParameter := congrArg (drawing.liftedStraightSegment index (0,0)).rationalXParameter crossing.2
  have recovered := (GridSegment.rationalXParameter_xAtParameter nonvertical
    (if crossingExit then (crossingEdgePiece graph drawing index line).finish else (crossingEdgePiece graph drawing index line).start)).symm.trans crossingParameter
  exact rectangleParameter.trans recovered.symm

theorem rectangle_before_crossing_contact {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (index column : Nat) (cell : Cell) (line : Int) {piece : EdgeRoutePiece}
    (lookup : rectangleEdgePiece? graph drawing index column cell = some piece)
    (crosses : (drawing.liftedStraightSegment index (0,0)).CrossesVerticalLine line)
    (ordered : piece.finish ≤ (crossingEdgePiece graph drawing index line).start) {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains piece.route point)
    (barContains : GridPolyline.RealContains (crossingEdgePiece graph drawing index line).route point) :
    piece.finish = (crossingEdgePiece graph drawing index line).start ∧
      point = realCell (piece.route.getLast?.getD (0,0)) := by
  have nonvertical : (drawing.liftedStraightSegment index (0,0)).start.1 ≠
      (drawing.liftedStraightSegment index (0,0)).finish.1 := by rcases crosses with forward | backward <;> omega
  have rectanglePositive := (rectangleEdgePiece?_valid planar degree graphLocal straight index column cell lookup).2.1
  have crossingPositive := (crossingEdgePiece_interval_bounds planar straight index line crosses).2.1
  have endpoints := rectangleEdgePiece?_crossing_contact_endpoints planar degree graphLocal straight index column cell lookup line contains barContains
  rcases endpoints.1 with ⟨rectanglePoint,rectangleEnd,rectangleReal⟩ | ⟨rectanglePoint,rectangleEnd,rectangleReal⟩ <;>
    rcases endpoints.2 with ⟨barPoint,barEnd,barReal⟩ | ⟨barPoint,barEnd,barReal⟩
  all_goals have points := realCell_injective (rectangleReal.symm.trans barReal)
  · have parameters := crossing_rectangle_endpoint_parameters_eq planar degree graphLocal straight index column cell line lookup nonvertical false false
      (rectangleEnd.trans ((congrArg some points).trans barEnd.symm))
    simp only [Bool.false_eq_true,if_false] at parameters
    linarith
  · have parameters := crossing_rectangle_endpoint_parameters_eq planar degree graphLocal straight index column cell line lookup nonvertical false true
      (rectangleEnd.trans ((congrArg some points).trans barEnd.symm))
    simp only [Bool.false_eq_true,if_false,if_true] at parameters
    linarith
  · have parameters := crossing_rectangle_endpoint_parameters_eq planar degree graphLocal straight index column cell line lookup nonvertical true false
      (rectangleEnd.trans ((congrArg some points).trans barEnd.symm))
    refine ⟨parameters,?_⟩
    simpa only [rectangleEnd,Option.getD_some] using rectangleReal
  · have parameters := crossing_rectangle_endpoint_parameters_eq planar degree graphLocal straight index column cell line lookup nonvertical true true
      (rectangleEnd.trans ((congrArg some points).trans barEnd.symm))
    simp only [if_true] at parameters
    linarith

end LeanTrominoes.PeriodicGridDrawing
