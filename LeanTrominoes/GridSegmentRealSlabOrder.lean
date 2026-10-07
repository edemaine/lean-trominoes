/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GridSegmentRealAffineInterpolation

/-! # Noncrossing segments preserve their vertical order across a slab -/
namespace LeanTrominoes.GridSegment

theorem real_contact_of_reversed_slab_order {first second : GridSegment}
    {left right firstLeft firstRight secondLeft secondRight : ℝ}
    (width : left < right) (leftOrder : firstLeft < secondLeft) (rightOrder : secondRight < firstRight)
    (firstAtLeft : first.RealContains (left,firstLeft)) (firstAtRight : first.RealContains (right,firstRight))
    (secondAtLeft : second.RealContains (left,secondLeft)) (secondAtRight : second.RealContains (right,secondRight)) :
    ∃ point : ℝ × ℝ, left < point.1 ∧ point.1 < right ∧ first.RealContains point ∧ second.RealContains point := by
  let denominator := (secondLeft-firstLeft)+(firstRight-secondRight)
  have positive : 0 < denominator := by dsimp [denominator]; linarith
  let parameter := (secondLeft-firstLeft)/denominator
  have lower : 0 < parameter := div_pos (by linarith) positive
  have upper : parameter < 1 := by
    apply (div_lt_one positive).mpr
    dsimp [denominator]
    linarith
  have cancel : parameter*denominator = secondLeft-firstLeft := div_mul_cancel₀ _ positive.ne'
  have heightEq : (1-parameter)*firstLeft+parameter*firstRight =
      (1-parameter)*secondLeft+parameter*secondRight := by
    dsimp [denominator] at cancel
    nlinarith [cancel]
  refine ⟨((1-parameter)*left+parameter*right,(1-parameter)*firstLeft+parameter*firstRight),?_,?_,
    firstAtLeft.interpolate firstAtRight lower.le upper.le,?_⟩
  · dsimp only [Prod.fst]
    nlinarith [mul_pos lower (sub_pos.mpr width)]
  · dsimp only [Prod.fst]
    nlinarith [mul_pos (sub_pos.mpr upper) (sub_pos.mpr width)]
  · rw [heightEq]
    exact secondAtLeft.interpolate secondAtRight lower.le upper.le

theorem real_slab_order_preserved {first second : GridSegment}
    {left right firstLeft firstRight secondLeft secondRight : ℝ}
    (width : left < right) (leftOrder : firstLeft < secondLeft)
    (firstAtLeft : first.RealContains (left,firstLeft)) (firstAtRight : first.RealContains (right,firstRight))
    (secondAtLeft : second.RealContains (left,secondLeft)) (secondAtRight : second.RealContains (right,secondRight))
    (disjoint : ∀ point : ℝ × ℝ, left < point.1 → point.1 < right →
      first.RealContains point → second.RealContains point → False) : firstRight ≤ secondRight := by
  by_contra reversed
  obtain ⟨point,lo,hi,fc,sc⟩ := real_contact_of_reversed_slab_order width leftOrder (by linarith)
    firstAtLeft firstAtRight secondAtLeft secondAtRight
  exact disjoint point lo hi fc sc

theorem real_slab_order_strict {first second : GridSegment}
    {left right firstLeft firstRight secondLeft secondRight : ℝ}
    (width : left < right) (leftOrder : firstLeft < secondLeft)
    (firstAtLeft : first.RealContains (left,firstLeft)) (firstAtRight : first.RealContains (right,firstRight))
    (secondAtLeft : second.RealContains (left,secondLeft)) (secondAtRight : second.RealContains (right,secondRight))
    (disjoint : ∀ point : ℝ × ℝ, left < point.1 → point.1 ≤ right →
      first.RealContains point → second.RealContains point → False) : firstRight < secondRight := by
  have order := real_slab_order_preserved width leftOrder firstAtLeft firstAtRight secondAtLeft secondAtRight
    (fun point lo hi => disjoint point lo hi.le)
  by_contra different
  have equal : firstRight = secondRight := by linarith
  apply disjoint (right,firstRight) width le_rfl firstAtRight
  simpa only [equal] using secondAtRight

end LeanTrominoes.GridSegment
