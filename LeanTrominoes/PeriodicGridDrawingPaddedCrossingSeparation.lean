/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingPaddedCrossingRoutes
import LeanTrominoes.PeriodicGridDrawingVerticalCrossingDistinctness

/-! # A shared point of actual crossing bars identifies the original edge occurrence -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement

theorem paddedCrossingRoutes_contact_identifies_occurrence {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {first last : PeriodicEdge Vertex × Nat} (firstMember : first ∈ graph.edges.zipIdx) (lastMember : last ∈ graph.edges.zipIdx)
    (firstCell lastCell : Cell) {firstLine lastLine : Int}
    (firstCrosses : (drawing.liftedStraightSegment first.2 firstCell).CrossesVerticalLine firstLine)
    (lastCrosses : (drawing.liftedStraightSegment last.2 lastCell).CrossesVerticalLine lastLine) {point : ℝ × ℝ}
    (firstContains : GridPolyline.RealContains (paddedCrossingRoute graph drawing firstLine (first.2,firstCell)) point)
    (lastContains : GridPolyline.RealContains (paddedCrossingRoute graph drawing lastLine (last.2,lastCell)) point) :
    firstLine = lastLine ∧ (first.2,firstCell) = (last.2,lastCell) := by
  have spacing : 10*(crossingBound drawing.gridSize : Int) < paddedRefinementFactor drawing.gridSize := by
    simp only [paddedRefinementFactor,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat]
    have nonnegative : (0 : Int) ≤ crossingBound drawing.gridSize := by positivity
    omega
  have contact := enlargedCrossingBars_contact_same_column spacing firstContains lastContains
  refine ⟨contact.1,?_⟩
  have lineEqual := contact.1
  subst lastLine
  have newHeightEqual : paddedPeriodicColumnHeight graph drawing firstLine
      ((drawing.liftedStraightSegment first.2 firstCell).rationalLineHeight firstLine) =
      paddedPeriodicColumnHeight graph drawing firstLine
        ((drawing.liftedStraightSegment last.2 lastCell).rationalLineHeight firstLine) := contact.2
  have firstLocal := graphLocal first.1 (List.fst_mem_of_mem_zipIdx firstMember)
  have lastLocal := graphLocal last.1 (List.fst_mem_of_mem_zipIdx lastMember)
  have oldHeightEqual : (drawing.liftedStraightSegment first.2 firstCell).rationalLineHeight firstLine =
      (drawing.liftedStraightSegment last.2 lastCell).rationalLineHeight firstLine := by
    by_contra different
    rcases lt_or_gt_of_ne different with before | after
    · have order := paddedPeriodicColumnHeight_preserves_order planar.1.1 degree firstMember lastMember
        (straight _ firstMember) (straight _ lastMember) firstLocal lastLocal firstCell lastCell firstCrosses lastCrosses before
      omega
    · have order := paddedPeriodicColumnHeight_preserves_order planar.1.1 degree lastMember firstMember
        (straight _ lastMember) (straight _ firstMember) lastLocal firstLocal lastCell firstCell lastCrosses firstCrosses after
      omega
  by_contra different
  have firstValid : first.2 < drawing.edgeRoutes.length := by
    rw [planar.1.1.2.2.1]
    exact List.snd_lt_of_mem_zipIdx firstMember
  have lastValid : last.2 < drawing.edgeRoutes.length := by
    rw [planar.1.1.2.2.1]
    exact List.snd_lt_of_mem_zipIdx lastMember
  exact vertical_crossing_heights_ne planar.2 firstValid lastValid (straight _ firstMember) (straight _ lastMember)
    firstCell lastCell different firstCrosses lastCrosses oldHeightEqual

end LeanTrominoes.PeriodicGridDrawing
