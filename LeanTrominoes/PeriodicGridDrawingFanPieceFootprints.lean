/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingEdgePieceColumnCoverage

/-! # Fan intervals remain within the cut strips at their original endpoints -/
namespace LeanTrominoes.PeriodicGridDrawing
open RationalIntegerStripCover

theorem sourceEdgePiece_open_footprint {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (tagged : PeriodicEdge Vertex × Nat)
    (nonvertical : (drawing.liftedStraightSegment tagged.2 (0,0)).start.1 ≠ (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1)
    (parameter : ℚ) (after : (sourceEdgePiece graph drawing tagged).start < parameter)
    (before : parameter < (sourceEdgePiece graph drawing tagged).finish) :
    CutContains (columnPerturbation graph drawing) (drawing.liftedStraightSegment tagged.2 (0,0)).start.1
      ((drawing.liftedStraightSegment tagged.2 (0,0)).rationalPointAtParameter parameter).1 := by
  let segment := drawing.liftedStraightSegment tagged.2 (0,0)
  let coordinate := (segment.rationalPointAtParameter parameter).1
  have positive := columnPerturbation_positive planar straight
  have sourceParameter : segment.rationalXParameter segment.start.1 = 0 := by simp [GridSegment.rationalXParameter]
  have parameterEq : segment.rationalXParameter coordinate = parameter := GridSegment.rationalXParameter_xAtParameter nonvertical parameter
  change 0 < parameter at after
  change parameter < edgeFanParameter graph drawing tagged.2 at before
  change segment.start.1 ≠ segment.finish.1 at nonvertical
  have sourceBefore : segment.rationalXParameter segment.start.1 ≤ segment.rationalXParameter coordinate := by
    rw [sourceParameter,parameterEq]
    exact after.le
  rcases lt_or_gt_of_ne nonvertical with forward | backward
  · have cuts := edgeFanParameter_forward_cuts graph drawing tagged.2 forward
    have coordinateBefore : segment.rationalXParameter coordinate ≤
        segment.rationalXParameter ((segment.start.1 : ℚ)+columnPerturbation graph drawing) := by
      rw [parameterEq,cuts.1]
      exact before.le
    have lower := (GridSegment.rationalXParameter_le_iff forward _ _).mp sourceBefore
    have upper := (GridSegment.rationalXParameter_le_iff forward _ _).mp coordinateBefore
    exact ⟨by linarith,upper⟩
  · have cuts := edgeFanParameter_backward_cuts graph drawing tagged.2 backward
    have coordinateBefore : segment.rationalXParameter coordinate ≤
        segment.rationalXParameter ((segment.start.1 : ℚ)-columnPerturbation graph drawing) := by
      rw [parameterEq,cuts.1]
      exact before.le
    have upper := (GridSegment.rationalXParameter_le_iff_of_reverse backward _ _).mp sourceBefore
    have lower := (GridSegment.rationalXParameter_le_iff_of_reverse backward _ _).mp coordinateBefore
    exact ⟨lower,by linarith⟩

theorem targetEdgePiece_open_footprint {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (tagged : PeriodicEdge Vertex × Nat)
    (nonvertical : (drawing.liftedStraightSegment tagged.2 (0,0)).start.1 ≠ (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1)
    (parameter : ℚ) (after : (targetEdgePiece graph drawing tagged).start < parameter)
    (before : parameter < (targetEdgePiece graph drawing tagged).finish) :
    CutContains (columnPerturbation graph drawing) (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1
      ((drawing.liftedStraightSegment tagged.2 (0,0)).rationalPointAtParameter parameter).1 := by
  let segment := drawing.liftedStraightSegment tagged.2 (0,0)
  let coordinate := (segment.rationalPointAtParameter parameter).1
  have positive := columnPerturbation_positive planar straight
  change segment.start.1 ≠ segment.finish.1 at nonvertical
  have denominatorNonzero : (segment.finish.1 : ℚ)-(segment.start.1 : ℚ) ≠ 0 := by
    intro zero
    apply nonvertical
    exact_mod_cast (by linarith : (segment.start.1 : ℚ) = segment.finish.1)
  have finishParameter : segment.rationalXParameter segment.finish.1 = 1 := by
    simp only [GridSegment.rationalXParameter,div_self denominatorNonzero]
  have parameterEq : segment.rationalXParameter coordinate = parameter := GridSegment.rationalXParameter_xAtParameter nonvertical parameter
  change 1-edgeFanParameter graph drawing tagged.2 < parameter at after
  change parameter < 1 at before
  have beforeFinish : segment.rationalXParameter coordinate ≤ segment.rationalXParameter segment.finish.1 := by
    rw [parameterEq,finishParameter]
    exact before.le
  rcases lt_or_gt_of_ne nonvertical with forward | backward
  · have cuts := edgeFanParameter_forward_cuts graph drawing tagged.2 forward
    have coordinateAfter : segment.rationalXParameter ((segment.finish.1 : ℚ)-columnPerturbation graph drawing) ≤
        segment.rationalXParameter coordinate := by
      rw [parameterEq,cuts.2]
      exact after.le
    have lower := (GridSegment.rationalXParameter_le_iff forward _ _).mp coordinateAfter
    have upper := (GridSegment.rationalXParameter_le_iff forward _ _).mp beforeFinish
    exact ⟨lower,by linarith⟩
  · have cuts := edgeFanParameter_backward_cuts graph drawing tagged.2 backward
    have coordinateAfter : segment.rationalXParameter ((segment.finish.1 : ℚ)+columnPerturbation graph drawing) ≤
        segment.rationalXParameter coordinate := by
      rw [parameterEq,cuts.2]
      exact after.le
    have upper := (GridSegment.rationalXParameter_le_iff_of_reverse backward _ _).mp coordinateAfter
    have lower := (GridSegment.rationalXParameter_le_iff_of_reverse backward _ _).mp beforeFinish
    exact ⟨by linarith,upper⟩

end LeanTrominoes.PeriodicGridDrawing
