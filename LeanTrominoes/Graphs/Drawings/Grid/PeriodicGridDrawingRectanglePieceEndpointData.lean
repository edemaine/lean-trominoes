/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingEdgePieceBoundaryPorts
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingRectangleRowPortJoins

/-! # Each computed rectangle-piece endpoint has a verified port and old position -/
namespace LeanTrominoes.PeriodicGridDrawing

theorem rectangleEdgePiece?_endpoint_data {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (index column : Nat) (cell : Cell) {piece : EdgeRoutePiece}
    (lookup : rectangleEdgePiece? graph drawing index column cell = some piece) (exit : Bool) :
    ∃ key : RectanglePortKey Vertex, key.Valid graph drawing column ∧
      key.parentKey = (index,Cell.scale (-1) cell) ∧
      (if exit then piece.route.getLast? else piece.route.head?) =
        some (rectangleLiftedPortPoint graph drawing column cell key) ∧
      (drawing.liftedStraightSegment index (0,0)).rationalPointAtParameter
          (if exit then piece.finish else piece.start) =
        rectanglePortOriginalPoint graph drawing column cell key := by
  cases chord : rectangleParentChord graph drawing column (index,Cell.scale (-1) cell) with
  | none => simp [rectangleEdgePiece?,chord] at lookup
  | some keys =>
    have data := rectangleParentChord_data graph drawing column (index,Cell.scale (-1) cell) chord
    have endpoints := rectangleEdgePiece?_boundary_ports index column cell lookup chord
    have oldPoints := rectangleEdgePiece?_endpoint_original_points planar graphLocal straight index column cell lookup chord
    cases exit
    · simp only [Bool.false_eq_true,if_false]
      refine ⟨if rectangleParentForward graph drawing column (index,Cell.scale (-1) cell) keys.1 keys.2 then keys.1 else keys.2,?_,?_,endpoints.1,oldPoints.1⟩
      all_goals split_ifs
      · exact data.1
      · exact data.2.1
      · exact data.2.2.1
      · exact data.2.2.2.1
    · simp only [if_true]
      refine ⟨if rectangleParentForward graph drawing column (index,Cell.scale (-1) cell) keys.1 keys.2 then keys.2 else keys.1,?_,?_,endpoints.2.1,oldPoints.2⟩
      all_goals split_ifs
      · exact data.2.1
      · exact data.1
      · exact data.2.2.2.1
      · exact data.2.2.1

end LeanTrominoes.PeriodicGridDrawing
