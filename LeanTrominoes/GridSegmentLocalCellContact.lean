/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRealLocalBounds

/-! # A cell intersecting a local edge's open coordinate box is an endpoint cell -/
namespace LeanTrominoes.GridSegment

theorem cell_index_bounds_of_overlap {period lower upper cell : Int} {point : ℚ}
    (positive : 0 < period)
    (globalBounds : (period : ℚ)*lower < point ∧ point < (period : ℚ)*(upper+1))
    (cellBounds : (period : ℚ)*cell ≤ point ∧ point ≤ (period : ℚ)*(cell+1)) :
    lower ≤ cell ∧ cell ≤ upper := by
  have periodPositive : (0 : ℚ) < period := by exact_mod_cast positive
  constructor
  · by_contra outside
    have gap : (cell : ℚ)+1 ≤ lower := by exact_mod_cast (by omega : cell+1 ≤ lower)
    nlinarith only [gap,periodPositive,globalBounds.1,cellBounds.2]
  · by_contra outside
    have gap : (upper : ℚ)+1 ≤ cell := by exact_mod_cast (by omega : upper+1 ≤ cell)
    nlinarith only [gap,periodPositive,globalBounds.2,cellBounds.1]

theorem cell_eq_endpoint_of_local_coordinate_bounds {offset cell : Cell}
    (localOffset : offset.1.natAbs+offset.2.natAbs ≤ 1)
    (xBounds : min 0 offset.1 ≤ cell.1 ∧ cell.1 ≤ max 0 offset.1)
    (yBounds : min 0 offset.2 ≤ cell.2 ∧ cell.2 ≤ max 0 offset.2) :
    cell = (0,0) ∨ cell = offset := by
  by_cases zero : cell = (0,0)
  · exact Or.inl zero
  apply Or.inr
  have nonzero : cell.1 ≠ 0 ∨ cell.2 ≠ 0 := by
    by_contra both
    push Not at both
    exact zero (Prod.ext both.1 both.2)
  have offsets := PeriodicOrthocrossing.offset_eq_of_span_le_one (⟨(),(),offset⟩ : PeriodicEdge Unit) localOffset
  rcases offsets with rfl | rfl | rfl | rfl | rfl
  all_goals norm_num at xBounds yBounds
  all_goals apply Prod.ext <;> omega

theorem local_coordinate_shifted_open_box {period source target offset : Int} {point shift : ℚ}
    (positive : 0 < period) (sourceBounds : 0 < source ∧ source < period)
    (targetBounds : 0 < target ∧ target < period) (shiftBounds : 0 ≤ shift ∧ shift < 1)
    (pointBounds : (min source (target+period*offset) : Int) ≤ point ∧
      point ≤ (max source (target+period*offset) : Int)) :
    (period : ℚ)*(min 0 offset : Int) < point+shift ∧
      point+shift < (period : ℚ)*((max 0 offset : Int)+1) := by
  have lowerInt : period*min 0 offset+1 ≤ min source (target+period*offset) := by
    apply le_min
    · nlinarith [min_le_left (0 : Int) offset]
    · nlinarith [min_le_right (0 : Int) offset]
  have upperInt : max source (target+period*offset) ≤ period*(max 0 offset+1)-1 := by
    apply max_le
    · nlinarith [le_max_left (0 : Int) offset]
    · nlinarith [le_max_right (0 : Int) offset]
  have lower : (period : ℚ)*(min 0 offset : Int)+1 ≤ (min source (target+period*offset) : Int) := by
    exact_mod_cast lowerInt
  have upper : (max source (target+period*offset) : Int) ≤ (period : ℚ)*((max 0 offset : Int)+1)-1 := by
    exact_mod_cast upperInt
  constructor <;> linarith [pointBounds.1,pointBounds.2,shiftBounds.1,shiftBounds.2]

theorem scaled_local_coordinate_endpoint_box {period factor source target offset : Int}
    (positive : 0 < period) (factorNonnegative : 0 ≤ factor)
    (sourceBounds : 0 < source ∧ source < period) (targetBounds : 0 < target ∧ target < period) :
    factor*period*min 0 offset ≤ min (factor*source) (factor*(target+period*offset)) ∧
      max (factor*source) (factor*(target+period*offset)) ≤ factor*period*(max 0 offset+1) := by
  have sourceLower : period*min 0 offset ≤ source := by nlinarith [min_le_left (0 : Int) offset]
  have targetLower : period*min 0 offset ≤ target+period*offset := by nlinarith [min_le_right (0 : Int) offset]
  have sourceUpper : source ≤ period*(max 0 offset+1) := by nlinarith [le_max_left (0 : Int) offset]
  have targetUpper : target+period*offset ≤ period*(max 0 offset+1) := by nlinarith [le_max_right (0 : Int) offset]
  constructor
  · exact le_min (by simpa [mul_assoc] using mul_le_mul_of_nonneg_left sourceLower factorNonnegative)
      (by simpa [mul_assoc] using mul_le_mul_of_nonneg_left targetLower factorNonnegative)
  · exact max_le (by simpa [mul_assoc] using mul_le_mul_of_nonneg_left sourceUpper factorNonnegative)
      (by simpa [mul_assoc] using mul_le_mul_of_nonneg_left targetUpper factorNonnegative)

end LeanTrominoes.GridSegment
