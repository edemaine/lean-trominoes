/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingEdgePieceEnumeration

/-! # Positive parameter intervals for every nonvertical replacement piece -/
namespace LeanTrominoes.PeriodicGridDrawing

theorem edgeFanParameter_bounds {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (index : Nat) (nonvertical : (drawing.liftedStraightSegment index (0,0)).start.1 ≠
      (drawing.liftedStraightSegment index (0,0)).finish.1) :
    0 < edgeFanParameter graph drawing index ∧ edgeFanParameter graph drawing index < 1/2 := by
  let segment := drawing.liftedStraightSegment index (0,0)
  change segment.start.1 ≠ segment.finish.1 at nonvertical
  have distance : (1 : ℚ) ≤ |(segment.finish.1 : ℚ)-(segment.start.1 : ℚ)| := by
    rcases lt_or_gt_of_ne nonvertical with forward | backward
    · have gap : segment.start.1+1 ≤ segment.finish.1 := by omega
      have rationalGap : (segment.start.1 : ℚ)+1 ≤ segment.finish.1 := by exact_mod_cast gap
      rw [abs_of_pos (by linarith : (0 : ℚ) < (segment.finish.1 : ℚ)-segment.start.1)]
      linarith
    · have gap : segment.finish.1+1 ≤ segment.start.1 := by omega
      have rationalGap : (segment.finish.1 : ℚ)+1 ≤ segment.start.1 := by exact_mod_cast gap
      rw [abs_of_neg (by linarith : (segment.finish.1 : ℚ)-(segment.start.1 : ℚ) < 0)]
      linarith
  have epsilonPositive := columnPerturbation_positive planar straight
  have epsilonSmall := (columnPerturbation_le_cutMargin planar straight).trans_lt (columnCutMargin_lt_half graph drawing)
  have distancePositive : (0 : ℚ) < |(segment.finish.1 : ℚ)-(segment.start.1 : ℚ)| := by linarith
  change 0 < columnPerturbation graph drawing / |(segment.finish.1 : ℚ)-(segment.start.1 : ℚ)| ∧
    columnPerturbation graph drawing / |(segment.finish.1 : ℚ)-(segment.start.1 : ℚ)| < 1/2
  exact ⟨div_pos epsilonPositive distancePositive,(div_lt_iff₀ distancePositive).mpr (by linarith)⟩

private theorem shifted_parameter_bounds {segment : GridSegment} {line : Int} {epsilon : ℚ}
    (crosses : segment.CrossesVerticalLine line) (small : |epsilon| < 1) :
    0 < segment.rationalXParameter ((line : ℚ)+epsilon) ∧
      segment.rationalXParameter ((line : ℚ)+epsilon) < 1 := by
  apply GridSegment.rationalXParameter_in_unit_interval
  have lo := (abs_lt.mp small).1
  have hi := (abs_lt.mp small).2
  rcases crosses with forward | backward
  · have lower : (segment.start.1 : ℚ)+1 ≤ line := by exact_mod_cast (by omega : segment.start.1+1 ≤ line)
    have upper : (line : ℚ)+1 ≤ segment.finish.1 := by exact_mod_cast (by omega : line+1 ≤ segment.finish.1)
    exact Or.inl ⟨by linarith,by linarith⟩
  · have lower : (segment.finish.1 : ℚ)+1 ≤ line := by exact_mod_cast (by omega : segment.finish.1+1 ≤ line)
    have upper : (line : ℚ)+1 ≤ segment.start.1 := by exact_mod_cast (by omega : line+1 ≤ segment.start.1)
    exact Or.inr ⟨by linarith,by linarith⟩

theorem crossingEdgePiece_interval_bounds {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (index : Nat) (line : Int)
    (crosses : (drawing.liftedStraightSegment index (0,0)).CrossesVerticalLine line) :
    0 < (crossingEdgePiece graph drawing index line).start ∧
      (crossingEdgePiece graph drawing index line).start < (crossingEdgePiece graph drawing index line).finish ∧
      (crossingEdgePiece graph drawing index line).finish < 1 := by
  have epsilonPositive := columnPerturbation_positive planar straight
  have epsilonSmall := (columnPerturbation_le_cutMargin planar straight).trans_lt (columnCutMargin_lt_half graph drawing)
  have small : |columnPerturbation graph drawing| < 1 := by rw [abs_of_pos epsilonPositive]; linarith
  have first := shifted_parameter_bounds crosses (show |-columnPerturbation graph drawing| < 1 by simpa using small)
  have last := shifted_parameter_bounds crosses small
  have nonvertical : (drawing.liftedStraightSegment index (0,0)).start.1 ≠
      (drawing.liftedStraightSegment index (0,0)).finish.1 := by rcases crosses with forward | backward <;> omega
  have distinct := (GridSegment.rationalXParameter_injective nonvertical).ne (show
      (line : ℚ)-columnPerturbation graph drawing ≠ (line : ℚ)+columnPerturbation graph drawing by linarith)
  change 0 < min _ _ ∧ min _ _ < max _ _ ∧ max _ _ < 1
  simp only [sub_eq_add_neg] at distinct ⊢
  exact ⟨lt_min first.1 last.1,min_lt_max.mpr distinct,max_lt first.2 last.2⟩

theorem nonverticalEdgePieces_interval_bounds {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (tagged : PeriodicEdge Vertex × Nat)
    (nonvertical : (drawing.liftedStraightSegment tagged.2 (0,0)).start.1 ≠
      (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1)
    {piece : EdgeRoutePiece} (member : piece ∈ nonverticalEdgePieces graph drawing tagged) :
    0 ≤ piece.start ∧ piece.start < piece.finish ∧ piece.finish ≤ 1 := by
  have fan := edgeFanParameter_bounds planar straight tagged.2 nonvertical
  simp only [nonverticalEdgePieces,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with ((source | rectangle) | crossing) | target
  · subst piece
    change (0 : ℚ) ≤ 0 ∧ 0 < edgeFanParameter graph drawing tagged.2 ∧ edgeFanParameter graph drawing tagged.2 ≤ 1
    exact ⟨le_rfl,fan.1,by linarith⟩
  · have bounds := rectangleEdgePieces_valid planar degree graphLocal straight tagged.2 rectangle
    exact ⟨bounds.1.le,bounds.2.1,bounds.2.2.1.le⟩
  · obtain ⟨line,_,lookup⟩ := List.mem_filterMap.mp crossing
    split_ifs at lookup with crosses
    have equal := Option.some.inj lookup
    subst piece
    have bounds := crossingEdgePiece_interval_bounds planar straight tagged.2 line crosses
    exact ⟨bounds.1.le,bounds.2.1,bounds.2.2.le⟩
  · subst piece
    change 0 ≤ 1-edgeFanParameter graph drawing tagged.2 ∧ 1-edgeFanParameter graph drawing tagged.2 < 1 ∧ (1 : ℚ) ≤ 1
    exact ⟨by linarith,by linarith,le_rfl⟩

end LeanTrominoes.PeriodicGridDrawing
