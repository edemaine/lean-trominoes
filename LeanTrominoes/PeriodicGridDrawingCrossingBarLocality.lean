/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingStraightLocalCoordinateBoxes
import LeanTrominoes.PeriodicGridDrawingRefinedLocalBoxes
import LeanTrominoes.PeriodicGridDrawingPaddedCrossingRoutes
import LeanTrominoes.PeriodicGridDrawingPaddedPeriodicColumnRefinement

/-! # A proper crossing bar stays in the local rectangle of its parent edge -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement

theorem paddedCrossingRoute_isRealLocal {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (compatible : drawing.IsCompatible graph) (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (straight : (drawing.edgeRoute tagged.2).length = 2) {line : Int}
    (crosses : (drawing.liftedStraightSegment tagged.2 (0,0)).CrossesVerticalLine line)
    {point : ℝ × ℝ} (contains : GridPolyline.RealContains (paddedCrossingRoute graph drawing line (tagged.2,(0,0))) point) :
    (straightRefinementDrawing graph drawing).RealPointInCell (0,0) point ∨
      (straightRefinementDrawing graph drawing).RealPointInCell tagged.1.offset point := by
  let height := (drawing.liftedStraightSegment tagged.2 (0,0)).rationalLineHeight line
  let row := rationalCell drawing.gridSize height
  let ordinate := paddedPeriodicColumnHeight graph drawing line height
  have oldContains := GridSegment.rationalLineHeight_realContains crosses
  have global := straightSegment_rational_local_coordinate_bounds compatible member
    (point := ((line : ℚ),height)) (by simpa using oldContains) 0 0 (by norm_num) (by norm_num)
  simp only [add_zero] at global
  have positive : (0 : Int) < drawing.gridSize := by exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
  have residue := rationalResidue_bounds positive height
  have rowBounds : min 0 tagged.1.offset.2 ≤ row ∧ row ≤ max 0 tagged.1.offset.2 := by
    apply GridSegment.cell_index_bounds_of_overlap positive global.2
    unfold rationalResidue at residue
    constructor <;> linarith [residue.1,residue.2]
  have lineLower : (drawing.gridSize : Int)*min 0 tagged.1.offset.1+1 ≤ line := by
    have below : (drawing.gridSize : Int)*min 0 tagged.1.offset.1 < line := by exact_mod_cast global.1.1
    omega
  have lineUpper : line ≤ (drawing.gridSize : Int)*(max 0 tagged.1.offset.1+1)-1 := by
    have above : line < (drawing.gridSize : Int)*(max 0 tagged.1.offset.1+1) := by exact_mod_cast global.1.2
    omega
  have clearance := paddedPeriodicColumnHeight_row_clearance compatible degree member straight
    (graphLocal _ (List.fst_mem_of_mem_zipIdx member)) (0,0) crosses
  change (paddedGridSize drawing.gridSize : Int)*row+(30*crossingBound drawing.gridSize+10) < ordinate ∧
    ordinate < (paddedGridSize drawing.gridSize : Int)*(row+1)-(30*crossingBound drawing.gridSize+10) at clearance
  have gridNonnegative : (0 : Int) ≤ paddedGridSize drawing.gridSize := by positivity
  have rowLower := mul_le_mul_of_nonneg_left rowBounds.1 gridNonnegative
  have rowUpper := mul_le_mul_of_nonneg_left (by omega : row+1 ≤ max 0 tagged.1.offset.2+1) gridNonnegative
  have ordinateLower : (paddedGridSize drawing.gridSize : Int)*min 0 tagged.1.offset.2 ≤ ordinate := by
    have nonnegative : (0 : Int) ≤ crossingBound drawing.gridSize := by positivity
    omega
  have ordinateUpper : ordinate ≤ (paddedGridSize drawing.gridSize : Int)*(max 0 tagged.1.offset.2+1) := by
    have nonnegative : (0 : Int) ≤ crossingBound drawing.gridSize := by positivity
    omega
  have factorPositive : (0 : Int) < paddedRefinementFactor drawing.gridSize := by exact_mod_cast paddedRefinementFactor_positive drawing.gridSize
  have lowerScaled := mul_le_mul_of_nonneg_left lineLower factorPositive.le
  have upperScaled := mul_le_mul_of_nonneg_left lineUpper factorPositive.le
  have lowerReal : (paddedRefinementFactor drawing.gridSize : ℝ)*
      ((drawing.gridSize : ℝ)*(min 0 tagged.1.offset.1 : Int)+1) ≤ (paddedRefinementFactor drawing.gridSize : ℝ)*line := by exact_mod_cast lowerScaled
  have upperReal : (paddedRefinementFactor drawing.gridSize : ℝ)*line ≤ (paddedRefinementFactor drawing.gridSize : ℝ)*
      ((drawing.gridSize : ℝ)*((max 0 tagged.1.offset.1 : Int)+1)-1) := by exact_mod_cast upperScaled
  have room : 5*(crossingBound drawing.gridSize : ℝ) < paddedRefinementFactor drawing.gridSize := by
    have spacing : 5*(crossingBound drawing.gridSize : Int) < paddedRefinementFactor drawing.gridSize := by
      simp only [paddedRefinementFactor,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat]
      have nonnegative : (0 : Int) ≤ crossingBound drawing.gridSize := by positivity
      omega
    exact_mod_cast spacing
  have barBounds := enlargedCrossingBar_real_bounds _ _ _ _ contains
  simp only [Int.cast_natCast] at barBounds
  apply refined_real_local_of_coordinate_box graph drawing (graphLocal _ (List.fst_mem_of_mem_zipIdx member))
  refine ⟨?_,?_,?_,?_⟩
  · simp only [paddedGridSize,Nat.cast_mul]
    nlinarith [(abs_le.mp barBounds.1).1,(abs_le.mp barBounds.1).2]
  · simp only [paddedGridSize,Nat.cast_mul]
    nlinarith [(abs_le.mp barBounds.1).1,(abs_le.mp barBounds.1).2]
  · rw [barBounds.2]
    exact_mod_cast ordinateLower
  · rw [barBounds.2]
    exact_mod_cast ordinateUpper

end LeanTrominoes.PeriodicGridDrawing
