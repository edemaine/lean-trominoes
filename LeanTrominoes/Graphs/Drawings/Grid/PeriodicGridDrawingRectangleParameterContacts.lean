/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingRectangleNewPortSeamContacts
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingRectanglePieceEndpointData

/-! # Equal new rectangle endpoints have equal original edge parameters -/
namespace LeanTrominoes.PeriodicGridDrawing

theorem rectangle_horizontal_parent_prototype_nonhorizontal {Vertex : Type*}
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (index column : Nat) (cell : Cell) (top : Bool) {raw : Nat × Cell}
    (valid : (RectanglePortKey.horizontal top raw).Valid graph drawing column)
    (parent : (RectanglePortKey.horizontal (Vertex := Vertex) top raw).parentKey = (index,Cell.scale (-1) cell)) :
    (drawing.liftedStraightSegment index (0,0)).start.2 ≠ (drawing.liftedStraightSegment index (0,0)).finish.2 := by
  have horizontalMember := (List.mem_filter.mp valid.1).1
  have crosses := (of_decide_eq_true (List.mem_filter.mp horizontalMember).2).1
  change ((drawing.liftedStraightSegment raw.1 raw.2).start.2 < 0 ∧ 0 < (drawing.liftedStraightSegment raw.1 raw.2).finish.2) ∨
    ((drawing.liftedStraightSegment raw.1 raw.2).finish.2 < 0 ∧ 0 < (drawing.liftedStraightSegment raw.1 raw.2).start.2) at crosses
  have different : (drawing.liftedStraightSegment raw.1 raw.2).start.2 ≠
      (drawing.liftedStraightSegment raw.1 raw.2).finish.2 := by rcases crosses with forward | backward <;> omega
  have indexEq := congrArg Prod.fst parent
  change raw.1 = index at indexEq
  simp only [liftedStraightSegment,GridSegment.translate,Cell.add] at different ⊢
  rw [indexEq] at different
  omega

theorem rectangle_rectangle_endpoint_parameters_eq {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (index firstColumn lastColumn : Nat) (firstBound : firstColumn < drawing.gridSize) (lastBound : lastColumn < drawing.gridSize)
    (firstCell lastCell : Cell) {firstPiece lastPiece : EdgeRoutePiece}
    (firstLookup : rectangleEdgePiece? graph drawing index firstColumn firstCell = some firstPiece)
    (lastLookup : rectangleEdgePiece? graph drawing index lastColumn lastCell = some lastPiece)
    (different : (firstColumn,firstCell) ≠ (lastColumn,lastCell)) (firstExit lastExit : Bool)
    (sameEndpoint : (if firstExit then firstPiece.route.getLast? else firstPiece.route.head?) =
      (if lastExit then lastPiece.route.getLast? else lastPiece.route.head?)) :
    (if firstExit then firstPiece.finish else firstPiece.start) =
      (if lastExit then lastPiece.finish else lastPiece.start) := by
  obtain ⟨first,firstValid,firstParent,firstEnd,firstOld⟩ := rectangleEdgePiece?_endpoint_data planar graphLocal straight index firstColumn firstCell firstLookup firstExit
  obtain ⟨last,lastValid,_,lastEnd,lastOld⟩ := rectangleEdgePiece?_endpoint_data planar graphLocal straight index lastColumn lastCell lastLookup lastExit
  have positions := Option.some.inj (firstEnd.symm.trans (sameEndpoint.trans lastEnd))
  obtain ⟨oldY,top,raw,keyEq⟩ := rectangle_distinct_integral_ports_old_y_eq planar degree graphLocal straight
    firstColumn lastColumn firstBound lastBound firstCell lastCell firstValid lastValid different positions
  rw [keyEq] at firstValid firstParent
  have differentY := rectangle_horizontal_parent_prototype_nonhorizontal index firstColumn firstCell top firstValid firstParent
  have denominator : ((drawing.liftedStraightSegment index (0,0)).finish.2 : ℚ)-
      (drawing.liftedStraightSegment index (0,0)).start.2 ≠ 0 := by
    apply sub_ne_zero.mpr
    exact_mod_cast differentY.symm
  have coordinates := (congrArg Prod.snd firstOld).trans (oldY.trans (congrArg Prod.snd lastOld).symm)
  simp only [GridSegment.rationalPointAtParameter] at coordinates
  apply mul_right_cancel₀ denominator
  linarith

end LeanTrominoes.PeriodicGridDrawing
