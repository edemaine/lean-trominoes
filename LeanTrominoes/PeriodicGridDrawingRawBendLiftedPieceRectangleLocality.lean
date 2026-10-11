/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRawBendPieceRectangleLocality
import LeanTrominoes.PeriodicGridDrawingRawBendLiftedPieceRoutes

/-! # Rectangle locality of full piece routes in periodic copies -/
namespace LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
open PeriodicGraph.BendSubdivision OrthogonalDrawingRefinement PeriodicOrthocrossing

theorem liftedPieceRoute_inside_rectangle {V : Type*} [DecidableEq V]
    {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing source)
    {tagged : PeriodicEdge (Vertex V) × Nat}
    (member : tagged ∈ (subdivisionGraph source drawing).edges.zipIdx) (copy : Cell)
    {left right bottom top : ℝ}
    (fanBounds : ∀ target point, GridPolyline.RealContains (liftedPieceFan source drawing tagged target copy) point →
      left ≤ point.1 ∧ point.1 ≤ right ∧ bottom ≤ point.2 ∧ point.2 ≤ top)
    {point : ℝ × ℝ} (contains : GridPolyline.RealContains (liftedPieceRoute source drawing tagged copy) point) :
    left ≤ point.1 ∧ point.1 ≤ right ∧ bottom ≤ point.2 ∧ point.2 ≤ top := by
  let offset := Cell.scale (cubicScale drawing*drawing.gridSize) copy
  have shiftedContains : GridPolyline.RealContains (pieceRoute source drawing tagged)
      (point.1-offset.1,point.2-offset.2) :=
    (GridPolyline.realContains_translate_inverse offset _ point).mp contains
  have shiftedFanBounds (target : Bool) (p : ℝ × ℝ)
      (hasPoint : GridPolyline.RealContains (fanAt source drawing (Cubic.coreFactor drawing.gridSize)
        (Cubic.rasterFactor drawing.gridSize) (incidentRawSegment source drawing tagged target).start
          (incidentPort tagged target)) p) :
      left-offset.1 ≤ p.1 ∧ p.1 ≤ right-offset.1 ∧ bottom-offset.2 ≤ p.2 ∧ p.2 ≤ top-offset.2 := by
    have lifted : GridPolyline.RealContains (liftedPieceFan source drawing tagged target copy)
        (p.1+offset.1,p.2+offset.2) := by
      rw [liftedPieceFan_contains]
      simpa only [offset,add_sub_cancel_right] using hasPoint
    have bounds := fanBounds target _ lifted
    exact ⟨by linarith [bounds.1],by linarith [bounds.2.1],
      by linarith [bounds.2.2.1],by linarith [bounds.2.2.2]⟩
  have bounds := pieceRoute_inside_rectangle planar member
    (fun p hasPoint => shiftedFanBounds false p (by simpa only [pieceSourceFan,incidentRawSegment,
      incidentPort,Bool.false_eq_true,ite_false] using hasPoint))
    (fun p hasPoint => shiftedFanBounds true p (by simpa only [pieceTargetFan,GridPolyline.realContains_reverse,
      incidentRawSegment,incidentPort,ite_true,GridSegment.reverse] using hasPoint)) shiftedContains
  exact ⟨by linarith [bounds.1],by linarith [bounds.2.1],
    by linarith [bounds.2.2.1],by linarith [bounds.2.2.2]⟩

end LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
