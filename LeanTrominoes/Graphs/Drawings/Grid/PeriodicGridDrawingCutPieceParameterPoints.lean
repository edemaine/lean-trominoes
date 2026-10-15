/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingEdgePieceColumnCoverage

/-! # Fan and crossing interval endpoints recover their exact original cut coordinates -/
namespace LeanTrominoes.PeriodicGridDrawing

theorem crossingEdgePiece_endpoint_original_x {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (index : Nat) (line : Int)
    (nonvertical : (drawing.liftedStraightSegment index (0,0)).start.1 ≠ (drawing.liftedStraightSegment index (0,0)).finish.1) :
    ((drawing.liftedStraightSegment index (0,0)).rationalPointAtParameter (crossingEdgePiece graph drawing index line).start).1 =
      (line : ℚ)+(if (drawing.liftedStraightSegment index (0,0)).start.1 < (drawing.liftedStraightSegment index (0,0)).finish.1
        then -columnPerturbation graph drawing else columnPerturbation graph drawing) ∧
    ((drawing.liftedStraightSegment index (0,0)).rationalPointAtParameter (crossingEdgePiece graph drawing index line).finish).1 =
      (line : ℚ)+(if (drawing.liftedStraightSegment index (0,0)).start.1 < (drawing.liftedStraightSegment index (0,0)).finish.1
        then columnPerturbation graph drawing else -columnPerturbation graph drawing) := by
  have positive := columnPerturbation_positive planar straight
  have coordinates : (line : ℚ)-columnPerturbation graph drawing < (line : ℚ)+columnPerturbation graph drawing := by linarith
  rcases lt_or_gt_of_ne nonvertical with forward | backward
  · have ordered := (GridSegment.rationalXParameter_lt_iff forward _ _).mpr coordinates
    simp only [crossingEdgePiece,GridSegment.rationalPointAtParameter,if_pos forward,
      min_eq_left ordered.le,max_eq_right ordered.le]
    rw [GridSegment.rationalXAtParameter_parameter _ _ nonvertical,GridSegment.rationalXAtParameter_parameter _ _ nonvertical]
    simp only [sub_eq_add_neg,and_self]
  · have ordered := (GridSegment.rationalXParameter_lt_iff_of_reverse backward _ _).mpr coordinates
    have notForward : ¬(drawing.liftedStraightSegment index (0,0)).start.1 < (drawing.liftedStraightSegment index (0,0)).finish.1 := by omega
    simp only [crossingEdgePiece,GridSegment.rationalPointAtParameter,if_neg notForward,
      min_eq_right ordered.le,max_eq_left ordered.le]
    rw [GridSegment.rationalXAtParameter_parameter _ _ nonvertical,GridSegment.rationalXAtParameter_parameter _ _ nonvertical]
    simp only [sub_eq_add_neg,and_self]

theorem sourceEdgePiece_finish_original_x {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) (tagged : PeriodicEdge Vertex × Nat)
    (nonvertical : (drawing.liftedStraightSegment tagged.2 (0,0)).start.1 ≠ (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1) :
    ((drawing.liftedStraightSegment tagged.2 (0,0)).rationalPointAtParameter (sourceEdgePiece graph drawing tagged).finish).1 =
      (drawing.liftedStraightSegment tagged.2 (0,0)).start.1+
        (if (drawing.liftedStraightSegment tagged.2 (0,0)).start.1 < (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1
          then columnPerturbation graph drawing else -columnPerturbation graph drawing) := by
  rcases lt_or_gt_of_ne nonvertical with forward | backward
  · have cut := (edgeFanParameter_forward_cuts graph drawing tagged.2 forward).1
    change (drawing.liftedStraightSegment tagged.2 (0,0)).rationalXAtParameter (edgeFanParameter graph drawing tagged.2) = _
    rw [← cut,GridSegment.rationalXAtParameter_parameter _ _ nonvertical,if_pos forward]
  · have cut := (edgeFanParameter_backward_cuts graph drawing tagged.2 backward).1
    have notForward : ¬(drawing.liftedStraightSegment tagged.2 (0,0)).start.1 < (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1 := by omega
    change (drawing.liftedStraightSegment tagged.2 (0,0)).rationalXAtParameter (edgeFanParameter graph drawing tagged.2) = _
    rw [← cut,GridSegment.rationalXAtParameter_parameter _ _ nonvertical,if_neg notForward]
    ring

theorem targetEdgePiece_start_original_x {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) (tagged : PeriodicEdge Vertex × Nat)
    (nonvertical : (drawing.liftedStraightSegment tagged.2 (0,0)).start.1 ≠ (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1) :
    ((drawing.liftedStraightSegment tagged.2 (0,0)).rationalPointAtParameter (targetEdgePiece graph drawing tagged).start).1 =
      (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1+
        (if (drawing.liftedStraightSegment tagged.2 (0,0)).start.1 < (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1
          then -columnPerturbation graph drawing else columnPerturbation graph drawing) := by
  rcases lt_or_gt_of_ne nonvertical with forward | backward
  · have cut := (edgeFanParameter_forward_cuts graph drawing tagged.2 forward).2
    change (drawing.liftedStraightSegment tagged.2 (0,0)).rationalXAtParameter (1-edgeFanParameter graph drawing tagged.2) = _
    rw [← cut,GridSegment.rationalXAtParameter_parameter _ _ nonvertical,if_pos forward]
    ring
  · have cut := (edgeFanParameter_backward_cuts graph drawing tagged.2 backward).2
    have notForward : ¬(drawing.liftedStraightSegment tagged.2 (0,0)).start.1 < (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1 := by omega
    change (drawing.liftedStraightSegment tagged.2 (0,0)).rationalXAtParameter (1-edgeFanParameter graph drawing tagged.2) = _
    rw [← cut,GridSegment.rationalXAtParameter_parameter _ _ nonvertical,if_neg notForward]

end LeanTrominoes.PeriodicGridDrawing
