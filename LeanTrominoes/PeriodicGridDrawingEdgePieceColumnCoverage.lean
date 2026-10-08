/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingCrossingPieceWindow
import LeanTrominoes.PeriodicGridDrawingEdgePieceIntervals
import LeanTrominoes.GridSegmentRationalXParameterOrder
import LeanTrominoes.RationalIntegerStripCover

/-! # Fans and crossing bars cover every parameter outside the open column slabs -/
namespace LeanTrominoes.PeriodicGridDrawing
open RationalIntegerStripCover

theorem edgeFanParameter_forward_cuts {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (index : Nat) (forward : (drawing.liftedStraightSegment index (0,0)).start.1 < (drawing.liftedStraightSegment index (0,0)).finish.1) :
    (drawing.liftedStraightSegment index (0,0)).rationalXParameter
        ((drawing.liftedStraightSegment index (0,0)).start.1+columnPerturbation graph drawing) = edgeFanParameter graph drawing index ∧
      (drawing.liftedStraightSegment index (0,0)).rationalXParameter
        ((drawing.liftedStraightSegment index (0,0)).finish.1-columnPerturbation graph drawing) = 1-edgeFanParameter graph drawing index := by
  have positive : (0 : ℚ) < ((drawing.liftedStraightSegment index (0,0)).finish.1 : ℚ)-
      (drawing.liftedStraightSegment index (0,0)).start.1 := by exact_mod_cast sub_pos.mpr forward
  simp only [edgeFanParameter,GridSegment.rationalXParameter,abs_of_pos positive]
  constructor
  · ring
  · field_simp
    ring

theorem edgeFanParameter_backward_cuts {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (index : Nat) (backward : (drawing.liftedStraightSegment index (0,0)).finish.1 < (drawing.liftedStraightSegment index (0,0)).start.1) :
    (drawing.liftedStraightSegment index (0,0)).rationalXParameter
        ((drawing.liftedStraightSegment index (0,0)).start.1-columnPerturbation graph drawing) = edgeFanParameter graph drawing index ∧
      (drawing.liftedStraightSegment index (0,0)).rationalXParameter
        ((drawing.liftedStraightSegment index (0,0)).finish.1+columnPerturbation graph drawing) = 1-edgeFanParameter graph drawing index := by
  have negative : ((drawing.liftedStraightSegment index (0,0)).finish.1 : ℚ)-
      (drawing.liftedStraightSegment index (0,0)).start.1 < 0 := by exact_mod_cast sub_neg.mpr backward
  simp only [edgeFanParameter,GridSegment.rationalXParameter,abs_of_neg negative]
  constructor <;> field_simp [negative.ne] <;> ring

theorem crossingEdgePiece_contains_parameter {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (index : Nat) (line : Int) (crosses : (drawing.liftedStraightSegment index (0,0)).CrossesVerticalLine line)
    (parameter : ℚ)
    (cut : CutContains (columnPerturbation graph drawing) line
      ((drawing.liftedStraightSegment index (0,0)).rationalXAtParameter parameter)) :
    (crossingEdgePiece graph drawing index line).start ≤ parameter ∧
      parameter ≤ (crossingEdgePiece graph drawing index line).finish := by
  have positive := columnPerturbation_positive planar straight
  have nonvertical : (drawing.liftedStraightSegment index (0,0)).start.1 ≠
      (drawing.liftedStraightSegment index (0,0)).finish.1 := by rcases crosses with forward | backward <;> omega
  have order : (line : ℚ)-columnPerturbation graph drawing ≤ (line : ℚ)+columnPerturbation graph drawing := by linarith
  have between := (GridSegment.rationalXParameter_between_iff nonvertical
    ((line : ℚ)-columnPerturbation graph drawing) ((line : ℚ)+columnPerturbation graph drawing)
    ((drawing.liftedStraightSegment index (0,0)).rationalXAtParameter parameter)).mpr
      (by simpa only [CutContains,min_eq_left order,max_eq_right order] using cut)
  simpa only [crossingEdgePiece,GridSegment.rationalXParameter_xAtParameter nonvertical] using between

theorem nonverticalEdgePieces_cover_outside_slabs {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (nonvertical : (drawing.liftedStraightSegment tagged.2 (0,0)).start.1 ≠ (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1)
    (parameter : ℚ) (lower : 0 ≤ parameter) (upper : parameter ≤ 1) :
    (∃ piece ∈ nonverticalEdgePieces graph drawing tagged, piece.start ≤ parameter ∧ parameter ≤ piece.finish) ∨
      ∃ column : Int, SlabInteriorContains (columnPerturbation graph drawing) column
        ((drawing.liftedStraightSegment tagged.2 (0,0)).rationalXAtParameter parameter) := by
  let segment := drawing.liftedStraightSegment tagged.2 (0,0)
  have sourceMember : sourceEdgePiece graph drawing tagged ∈ nonverticalEdgePieces graph drawing tagged := by simp [nonverticalEdgePieces]
  have targetMember : targetEdgePiece graph drawing tagged ∈ nonverticalEdgePieces graph drawing tagged := by simp [nonverticalEdgePieces]
  rcases cut_or_slab (columnPerturbation_positive planar straight) (coordinate := segment.rationalXAtParameter parameter) with cut | slab
  · obtain ⟨line,cut⟩ := cut
    left
    by_cases crosses : segment.CrossesVerticalLine line
    · have crossingMember := crossingEdgePiece_mem planar.1.1 graphLocal member line crosses
      have wholeMember : crossingEdgePiece graph drawing tagged.2 line ∈ nonverticalEdgePieces graph drawing tagged := by
        simp only [nonverticalEdgePieces,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
        exact Or.inl (Or.inr crossingMember)
      exact ⟨_,wholeMember,crossingEdgePiece_contains_parameter planar straight tagged.2 line crosses parameter cut⟩
    · change segment.start.1 ≠ segment.finish.1 at nonvertical
      rcases lt_or_gt_of_ne nonvertical with forward | backward
      · have cuts := edgeFanParameter_forward_cuts graph drawing tagged.2 forward
        have outside : line ≤ segment.start.1 ∨ segment.finish.1 ≤ line := by
          unfold GridSegment.CrossesVerticalLine at crosses
          omega
        rcases outside with before | after
        · have coordinateBound : segment.rationalXAtParameter parameter ≤ (segment.start.1 : ℚ)+columnPerturbation graph drawing := by
            have lineBound : (line : ℚ) ≤ segment.start.1 := by exact_mod_cast before
            linarith [cut.2]
          have parameterBound := (GridSegment.rationalXParameter_le_iff forward _ _).mpr coordinateBound
          rw [GridSegment.rationalXParameter_xAtParameter nonvertical,cuts.1] at parameterBound
          exact ⟨_,sourceMember,lower,parameterBound⟩
        · have coordinateBound : (segment.finish.1 : ℚ)-columnPerturbation graph drawing ≤ segment.rationalXAtParameter parameter := by
            have lineBound : (segment.finish.1 : ℚ) ≤ line := by exact_mod_cast after
            linarith [cut.1]
          have parameterBound := (GridSegment.rationalXParameter_le_iff forward _ _).mpr coordinateBound
          rw [GridSegment.rationalXParameter_xAtParameter nonvertical,cuts.2] at parameterBound
          exact ⟨_,targetMember,parameterBound,upper⟩
      · have cuts := edgeFanParameter_backward_cuts graph drawing tagged.2 backward
        have outside : line ≤ segment.finish.1 ∨ segment.start.1 ≤ line := by
          unfold GridSegment.CrossesVerticalLine at crosses
          omega
        rcases outside with before | after
        · have coordinateBound : segment.rationalXAtParameter parameter ≤ (segment.finish.1 : ℚ)+columnPerturbation graph drawing := by
            have lineBound : (line : ℚ) ≤ segment.finish.1 := by exact_mod_cast before
            linarith [cut.2]
          have parameterBound := (GridSegment.rationalXParameter_le_iff_of_reverse backward
            ((segment.finish.1 : ℚ)+columnPerturbation graph drawing) (segment.rationalXAtParameter parameter)).mpr coordinateBound
          rw [GridSegment.rationalXParameter_xAtParameter nonvertical,cuts.2] at parameterBound
          exact ⟨_,targetMember,parameterBound,upper⟩
        · have coordinateBound : (segment.start.1 : ℚ)-columnPerturbation graph drawing ≤ segment.rationalXAtParameter parameter := by
            have lineBound : (segment.start.1 : ℚ) ≤ line := by exact_mod_cast after
            linarith [cut.1]
          have parameterBound := (GridSegment.rationalXParameter_le_iff_of_reverse backward
            (segment.rationalXAtParameter parameter) ((segment.start.1 : ℚ)-columnPerturbation graph drawing)).mpr coordinateBound
          rw [GridSegment.rationalXParameter_xAtParameter nonvertical,cuts.1] at parameterBound
          exact ⟨_,sourceMember,lower,parameterBound⟩
  · exact Or.inr slab

end LeanTrominoes.PeriodicGridDrawing
