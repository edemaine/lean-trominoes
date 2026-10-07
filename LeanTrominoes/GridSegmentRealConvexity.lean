/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRealGeometry
import LeanTrominoes.GridSegmentRealLineCharacterization

/-! # A straight segment contains every segment between two of its points -/
namespace LeanTrominoes.GridSegment

theorem realContains_of_endpoints_contained {parent child : GridSegment}
    (start : parent.RealContains (realCell child.start))
    (finish : parent.RealContains (realCell child.finish)) {point : ℝ × ℝ}
    (contains : child.RealContains point) : parent.RealContains point := by
  obtain ⟨u,uLo,uHi,ux,uy⟩ := start
  obtain ⟨v,vLo,vHi,vx,vy⟩ := finish
  obtain ⟨t,tLo,tHi,tx,ty⟩ := contains
  simp only [realCell] at ux uy vx vy
  refine ⟨(1-t)*u+t*v,?_,?_,?_,?_⟩
  · exact add_nonneg (mul_nonneg (by linarith) uLo) (mul_nonneg tLo vLo)
  · have bound := add_nonneg (mul_nonneg (by linarith : 0 ≤ 1-t) (by linarith : 0 ≤ 1-u))
      (mul_nonneg tLo (by linarith : 0 ≤ 1-v))
    nlinarith
  · rw [ux,vx] at tx
    calc point.1 = _ := tx
         _ = (parent.start.1 : ℝ)+((1-t)*u+t*v)*(parent.finish.1-parent.start.1) := by ring
  · rw [uy,vy] at ty
    calc point.2 = _ := ty
         _ = (parent.start.2 : ℝ)+((1-t)*u+t*v)*(parent.finish.2-parent.start.2) := by ring

theorem realContains_of_contains {segment : GridSegment} {point : Cell}
    (contains : segment.Contains point) : segment.RealContains (realCell point) := by
  apply (realContains_iff_box_and_line _ _).mpr
  rcases contains with ⟨horizontal,fixed,between⟩ | ⟨vertical,fixed,between⟩
  · have fixedFinish := fixed.trans horizontal.1
    constructor
    · rcases between with forward | backward
      · simp only [RealBoxContains,realCell,horizontal.1,min_self,max_self]
        have order : segment.start.1 ≤ segment.finish.1 := by omega
        rw [min_eq_left order,max_eq_right order]
        exact ⟨by exact_mod_cast forward.1,by exact_mod_cast forward.2,by exact_mod_cast fixedFinish.ge,by exact_mod_cast fixedFinish.le⟩
      · simp only [RealBoxContains,realCell,horizontal.1,min_self,max_self]
        have order : segment.finish.1 ≤ segment.start.1 := by omega
        rw [min_eq_right order,max_eq_left order]
        exact ⟨by exact_mod_cast backward.1,by exact_mod_cast backward.2,by exact_mod_cast fixedFinish.ge,by exact_mod_cast fixedFinish.le⟩
    · simp [RealLineContains,realCell,fixed,horizontal.1]
  · have fixedFinish := fixed.trans vertical.1
    constructor
    · rcases between with forward | backward
      · simp only [RealBoxContains,realCell,vertical.1,min_self,max_self]
        have order : segment.start.2 ≤ segment.finish.2 := by omega
        rw [min_eq_left order,max_eq_right order]
        exact ⟨by exact_mod_cast fixedFinish.ge,by exact_mod_cast fixedFinish.le,by exact_mod_cast forward.1,by exact_mod_cast forward.2⟩
      · simp only [RealBoxContains,realCell,vertical.1,min_self,max_self]
        have order : segment.finish.2 ≤ segment.start.2 := by omega
        rw [min_eq_right order,max_eq_left order]
        exact ⟨by exact_mod_cast fixedFinish.ge,by exact_mod_cast fixedFinish.le,by exact_mod_cast backward.1,by exact_mod_cast backward.2⟩
    · simp [RealLineContains,realCell,fixed,vertical.1]

end LeanTrominoes.GridSegment
