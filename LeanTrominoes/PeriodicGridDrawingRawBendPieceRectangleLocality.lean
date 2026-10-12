/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRawBendPieceSimplicity
import LeanTrominoes.GridPolylineRealEndpointContainment

/-! # Rectangle locality of a full piece follows from its two endpoint fans

The digital middle stays in its endpoint box, so fan anchors inside the
parent rectangle suffice for the whole assembled piece.
-/
namespace LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
open PeriodicGraph.BendSubdivision PeriodicOrthocrossing

theorem pieceRoute_inside_rectangle {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source)
    {tagged : PeriodicEdge (Vertex V) × Nat} (member : tagged ∈ (subdivisionGraph source drawing).edges.zipIdx)
    {left right bottom top : ℝ}
    (sourceBounds : ∀ point, GridPolyline.RealContains (pieceSourceFan source drawing tagged) point →
      left ≤ point.1 ∧ point.1 ≤ right ∧ bottom ≤ point.2 ∧ point.2 ≤ top)
    (targetBounds : ∀ point, GridPolyline.RealContains (pieceTargetFan source drawing tagged) point →
      left ≤ point.1 ∧ point.1 ≤ right ∧ bottom ≤ point.2 ∧ point.2 ≤ top)
    {point : ℝ × ℝ} (contains : GridPolyline.RealContains (pieceRoute source drawing tagged) point) :
    left ≤ point.1 ∧ point.1 ≤ right ∧ bottom ≤ point.2 ∧ point.2 ≤ top := by
  rcases (pieceRoute_contains V source drawing tagged point).mp contains with firstContains | coreContains | lastContains
  · exact sourceBounds point firstContains
  · have firstAnchor := sourceBounds _ (GridPolyline.realContains_last (pieceSourceFan_simple planar member).1
      (pieceSourceFan_last source drawing tagged))
    have lastAnchor := targetBounds _ (GridPolyline.realContains_head (pieceTargetFan_simple planar member).1
      (pieceTargetFan_head source drawing tagged))
    have box := coreRoute_box source drawing tagged coreContains
    simp only [realCell] at firstAnchor lastAnchor
    simp only [GridSegment.RealBoxContains,Int.cast_min,Int.cast_max] at box
    exact ⟨(le_min firstAnchor.1 lastAnchor.1).trans box.1,
      box.2.1.trans (max_le firstAnchor.2.1 lastAnchor.2.1),
      (le_min firstAnchor.2.2.1 lastAnchor.2.2.1).trans box.2.2.1,
      box.2.2.2.trans (max_le firstAnchor.2.2.2 lastAnchor.2.2.2)⟩
  · exact targetBounds point lastContains

end LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
