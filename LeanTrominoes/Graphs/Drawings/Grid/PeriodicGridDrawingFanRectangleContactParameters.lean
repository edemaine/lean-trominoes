/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingFanRectangleParameterContacts
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingEdgePieceContactEndpoints

/-! # Every rectangle-fan contact recovers the outer fan parameter -/
namespace LeanTrominoes.PeriodicGridDrawing
open PeriodicOrthocrossing

theorem rectangle_fan_contact_parameter {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (column : Nat) (cell : Cell) {piece : EdgeRoutePiece}
    (lookup : rectangleEdgePiece? graph drawing tagged.2 column cell = some piece)
    (nonvertical : (drawing.liftedStraightSegment tagged.2 (0,0)).start.1 ≠
      (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1) (target : Bool) {point : ℝ × ℝ}
    (rectangleContains : GridPolyline.RealContains piece.route point)
    (fanContains : GridPolyline.RealContains (if target then (targetEdgePiece graph drawing tagged).route else (sourceEdgePiece graph drawing tagged).route) point) :
    (∃ rectangleExit : Bool,
      (if rectangleExit then piece.finish else piece.start) =
        (if target then (targetEdgePiece graph drawing tagged).start else (sourceEdgePiece graph drawing tagged).finish) ∧
      point = realCell ((if rectangleExit then piece.route.getLast? else piece.route.head?).getD (0,0))) ∧
    point = realCell ((if target then (targetEdgePiece graph drawing tagged).route.head? else (sourceEdgePiece graph drawing tagged).route.getLast?).getD (0,0)) := by
  have outer : point = realCell ((if target then (targetEdgePiece graph drawing tagged).route.head? else (sourceEdgePiece graph drawing tagged).route.getLast?).getD (0,0)) := by
    cases target
    · have raw := (sourceEdgePiece_lifted_image graph drawing tagged point).mp fanContains
      have contact := rectangleEdgePiece?_fan_outer_contact planar degree graphLocal straight tagged.2 column cell lookup
        (sourcePort_mem_allPorts graph member) (0,0) rectangleContains raw
      rw [liftedPaddedIncidenceRoute_eq_translate] at contact
      simpa [sourceEdgePiece,Cell.scale,translatePolyline_zero] using contact
    · have raw : GridPolyline.RealContains (liftedPaddedIncidenceRoute graph drawing (targetPort tagged.1 tagged.2) tagged.1.offset) point :=
        (GridPolyline.realContains_reverse _ _).mp fanContains
      have contact := rectangleEdgePiece?_fan_outer_contact planar degree graphLocal straight tagged.2 column cell lookup
        (targetPort_mem_allPorts graph member) tagged.1.offset rectangleContains raw
      simpa only [if_true,targetEdgePiece,List.head?_reverse] using contact
  have rectangleEndpoint : GridPolyline.RealIsEndpoint piece.route point := by
    cases target
    · exact (rectangleEdgePiece?_fan_contact_endpoints planar degree graphLocal straight tagged.2 column cell lookup
        (sourcePort_mem_allPorts graph member) (0,0) rectangleContains
        ((sourceEdgePiece_lifted_image graph drawing tagged point).mp fanContains)).1
    · exact (rectangleEdgePiece?_fan_contact_endpoints planar degree graphLocal straight tagged.2 column cell lookup
        (targetPort_mem_allPorts graph member) tagged.1.offset rectangleContains
        ((GridPolyline.realContains_reverse _ _).mp fanContains)).1
  have fanData := fanEdgePiece_outer_endpoint_data planar degree straight member nonvertical target
  cases fanEnd : (if target then (targetEdgePiece graph drawing tagged).route.head? else (sourceEdgePiece graph drawing tagged).route.getLast?) with
  | none => simp [fanEnd] at fanData
  | some fanPoint =>
    have pointAtFan : point = realCell fanPoint := by simpa only [fanEnd,Option.getD_some] using outer
    refine ⟨?_,by simpa only [fanEnd] using outer⟩
    rcases rectangleEndpoint with ⟨rectanglePoint,rectangleEnd,rectangleReal⟩ | ⟨rectanglePoint,rectangleEnd,rectangleReal⟩
    · have points := realCell_injective (rectangleReal.symm.trans pointAtFan)
      refine ⟨false,fan_rectangle_endpoint_parameters_eq planar degree graphLocal straight member column cell lookup nonvertical false target
        (rectangleEnd.trans ((congrArg some points).trans fanEnd.symm)),?_⟩
      simpa only [Bool.false_eq_true,if_false,rectangleEnd,Option.getD_some] using rectangleReal
    · have points := realCell_injective (rectangleReal.symm.trans pointAtFan)
      refine ⟨true,fan_rectangle_endpoint_parameters_eq planar degree graphLocal straight member column cell lookup nonvertical true target
        (rectangleEnd.trans ((congrArg some points).trans fanEnd.symm)),?_⟩
      simpa only [if_true,rectangleEnd,Option.getD_some] using rectangleReal

end LeanTrominoes.PeriodicGridDrawing
