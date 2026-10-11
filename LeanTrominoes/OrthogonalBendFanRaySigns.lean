/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.OrthogonalBendFanAssignment
import LeanTrominoes.GridSegmentSeparatingAxes

/-! # Fan sign classes preserve the coordinate signs of actual segment rays -/
namespace LeanTrominoes.OrthogonalDrawingRefinement.BendFan

theorem verticalSign_nonnegative {key : StraightRayKey} (bound : 0 ≤ outwardHeight key) :
    0 ≤ verticalSign key := by
  simp only [verticalSign,if_neg (not_lt_of_ge bound)]
  split_ifs <;> norm_num

theorem verticalSign_nonpositive {key : StraightRayKey} (bound : outwardHeight key ≤ 0) :
    verticalSign key ≤ 0 := by
  simp only [verticalSign,if_neg (not_lt_of_ge bound)]
  split_ifs <;> norm_num

theorem segment_horizontalSign_nonnegative {segment : GridSegment} (bound : 0 ≤ segment.direction.1) :
    0 ≤ horizontalSign segment.straightRayKey := by
  unfold GridSegment.straightRayKey
  split_ifs with right left up
  · norm_num [horizontalSign]
  · simp only [GridSegment.direction] at bound
    omega
  · norm_num [horizontalSign]
  · norm_num [horizontalSign]

theorem segment_horizontalSign_nonpositive {segment : GridSegment} (bound : segment.direction.1 ≤ 0) :
    horizontalSign segment.straightRayKey ≤ 0 := by
  unfold GridSegment.straightRayKey
  split_ifs with right left up
  · simp only [GridSegment.direction] at bound
    omega
  · norm_num [horizontalSign]
  · norm_num [horizontalSign]
  · norm_num [horizontalSign]

theorem segment_verticalSign_nonnegative {segment : GridSegment} (different : segment.start ≠ segment.finish)
    (bound : 0 ≤ segment.direction.2) : 0 ≤ verticalSign segment.straightRayKey := by
  have numerator : (0 : ℚ) ≤ (segment.finish.2 : ℚ)-segment.start.2 := by exact_mod_cast bound
  apply verticalSign_nonnegative
  unfold GridSegment.straightRayKey
  split_ifs with right left up
  · simp only [outwardHeight,GridSegment.rationalSlope]
    exact div_nonneg numerator (by exact_mod_cast (show 0 ≤ segment.finish.1-segment.start.1 by omega))
  · simp only [outwardHeight,GridSegment.rationalSlope]
    exact neg_nonneg.mpr (div_nonpos_of_nonneg_of_nonpos numerator
      (by exact_mod_cast (show segment.finish.1-segment.start.1 ≤ 0 by omega)))
  · norm_num [outwardHeight]
  · have sameX : segment.start.1 = segment.finish.1 := by omega
    have sameY : segment.start.2 = segment.finish.2 := by
      simp only [GridSegment.direction] at bound
      omega
    exact (different (Prod.ext sameX sameY)).elim

theorem segment_verticalSign_nonpositive {segment : GridSegment}
    (bound : segment.direction.2 ≤ 0) : verticalSign segment.straightRayKey ≤ 0 := by
  have numerator : (segment.finish.2 : ℚ)-segment.start.2 ≤ 0 := by exact_mod_cast bound
  apply verticalSign_nonpositive
  unfold GridSegment.straightRayKey
  split_ifs with right left up
  · simp only [outwardHeight,GridSegment.rationalSlope]
    exact div_nonpos_of_nonpos_of_nonneg numerator
      (by exact_mod_cast (show 0 ≤ segment.finish.1-segment.start.1 by omega))
  · simp only [outwardHeight,GridSegment.rationalSlope]
    exact neg_nonpos.mpr (div_nonneg_of_nonpos numerator
      (by exact_mod_cast (show segment.finish.1-segment.start.1 ≤ 0 by omega)))
  · simp only [GridSegment.direction] at bound
    omega
  · norm_num [outwardHeight]

end LeanTrominoes.OrthogonalDrawingRefinement.BendFan
