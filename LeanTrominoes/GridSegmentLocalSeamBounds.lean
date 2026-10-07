/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GridSegmentRationalHorizontalCrossing
import LeanTrominoes.GridSegmentRealIntersection

/-! # Local straight edges cannot cross a row seam at a column seam -/
namespace LeanTrominoes.GridSegment

theorem local_horizontal_seam_abscissa_bounds {period row : Int} {source target shift offset : Cell}
    (positive : 0 < period)
    (sourceBounds : 0 < source.1 ∧ source.1 < period ∧ 0 < source.2 ∧ source.2 < period)
    (targetBounds : 0 < target.1 ∧ target.1 < period ∧ 0 < target.2 ∧ target.2 < period)
    (edgeLocal : offset.1.natAbs+offset.2.natAbs ≤ 1)
    (crosses : (GridSegment.mk (Cell.add source (Cell.scale period shift))
      (Cell.add target (Cell.scale period (Cell.add shift offset)))).CrossesHorizontalLine (period*row)) :
    offset.1 = 0 ∧
      (period : ℚ)*shift.1 < (GridSegment.mk (Cell.add source (Cell.scale period shift))
        (Cell.add target (Cell.scale period (Cell.add shift offset)))).rationalLineAbscissa (period*row) ∧
      (GridSegment.mk (Cell.add source (Cell.scale period shift))
        (Cell.add target (Cell.scale period (Cell.add shift offset)))).rationalLineAbscissa (period*row) <
          (period : ℚ)*(shift.1+1) := by
  have nonzeroY : offset.2 ≠ 0 := by
    intro zeroY
    have crossed := crosses
    simp only [CrossesHorizontalLine,CrossesVerticalLine,swapAxes,Cell.add,Cell.scale,Prod.swap,zeroY,add_zero] at crossed
    have rowCases : row ≤ shift.2 ∨ shift.2+1 ≤ row := by omega
    rcases rowCases with before | after
    · have scaled := mul_le_mul_of_nonneg_left before positive.le
      rcases crossed with forward | backward <;> nlinarith [sourceBounds.2.2.1,targetBounds.2.2.1]
    · have scaled := mul_le_mul_of_nonneg_left after positive.le
      rcases crossed with forward | backward <;> nlinarith [sourceBounds.2.2.2,targetBounds.2.2.2]
  have positiveY : 0 < offset.2.natAbs := Int.natAbs_pos.mpr nonzeroY
  have zeroAbsX : offset.1.natAbs = 0 := by omega
  have zeroX : offset.1 = 0 := Int.natAbs_eq_zero.mp zeroAbsX
  have image := rationalLineAbscissa_realContains crosses
  have box := realBoxContains_of_realContains image
  simp only [RealBoxContains,Cell.add,Cell.scale,Prod.fst,Prod.snd,zeroX,add_zero] at box
  have lower : period*shift.1 < min (source.1+period*shift.1) (target.1+period*shift.1) :=
    lt_min (by omega) (by omega)
  have upper : max (source.1+period*shift.1) (target.1+period*shift.1) < period*(shift.1+1) := by
    apply max_lt <;> nlinarith [sourceBounds.2.1,targetBounds.2.1]
  have realLower : ((period*shift.1 : Int) : ℝ) <
      ((min (source.1+period*shift.1) (target.1+period*shift.1) : Int) : ℝ) := by exact_mod_cast lower
  have realUpper : ((max (source.1+period*shift.1) (target.1+period*shift.1) : Int) : ℝ) <
      ((period*(shift.1+1) : Int) : ℝ) := by exact_mod_cast upper
  refine ⟨zeroX,?_,?_⟩
  · have bound := lt_of_lt_of_le realLower box.1
    simp only [Cell.add,Cell.scale,zeroX,add_zero]
    exact_mod_cast bound
  · have bound := lt_of_le_of_lt box.2.1 realUpper
    simp only [Cell.add,Cell.scale,zeroX,add_zero]
    exact_mod_cast bound

end LeanTrominoes.GridSegment
