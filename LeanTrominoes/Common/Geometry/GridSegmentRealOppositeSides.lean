/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Common.Geometry.GridSegmentRealInteriorInterpolation

/-! # Opposite-side tests force a proper straight-segment intersection -/
namespace LeanTrominoes.GridSegment

def orientedArea (first last point : ℝ × ℝ) : ℝ :=
  (last.1-first.1)*(point.2-first.2)-(last.2-first.2)*(point.1-first.1)

theorem real_interior_contact_of_opposite_sides {first second : GridSegment}
    {a b c d : ℝ × ℝ}
    (firstStart : first.RealContains a) (firstEnd : first.RealContains b)
    (secondStart : second.RealContains c) (secondEnd : second.RealContains d)
    (cSide : orientedArea a b c < 0) (dSide : 0 < orientedArea a b d)
    (aSide : 0 < orientedArea c d a) (bSide : orientedArea c d b < 0) :
    ∃ point : ℝ × ℝ, first.RealInteriorContains point ∧ second.RealInteriorContains point := by
  let denominator := orientedArea a b d-orientedArea a b c
  have positive : 0 < denominator := by dsimp only [denominator]; linarith
  have denominatorEq : denominator = orientedArea c d a-orientedArea c d b := by
    dsimp [denominator,orientedArea]
    ring
  let t := orientedArea c d a/denominator
  let u := -orientedArea a b c/denominator
  have tLo : 0 < t := div_pos aSide positive
  have tHi : t < 1 := by
    apply (div_lt_one positive).mpr
    rw [denominatorEq]
    linarith
  have uLo : 0 < u := div_pos (neg_pos.mpr cSide) positive
  have uHi : u < 1 := by
    apply (div_lt_one positive).mpr
    dsimp only [denominator]
    linarith
  have samePoint : ((1-t)*a.1+t*b.1,(1-t)*a.2+t*b.2) =
      ((1-u)*c.1+u*d.1,(1-u)*c.2+u*d.2) := by
    apply Prod.ext
    all_goals
      dsimp only [t,u,Prod.fst,Prod.snd]
      field_simp [positive.ne']
      dsimp [denominator,orientedArea]
      ring
  have firstDifferent : a ≠ b := by
    intro equal
    subst b
    simp [orientedArea] at dSide
  have secondDifferent : c ≠ d := by
    intro equal
    subst d
    simp [orientedArea] at aSide
  refine ⟨_,firstStart.interpolate_interior firstEnd firstDifferent tLo tHi,?_⟩
  rw [samePoint]
  exact secondStart.interpolate_interior secondEnd secondDifferent uLo uHi

theorem real_contact_of_opposite_sides {first second : GridSegment}
    {a b c d : ℝ × ℝ}
    (firstStart : first.RealContains a) (firstEnd : first.RealContains b)
    (secondStart : second.RealContains c) (secondEnd : second.RealContains d)
    (cSide : orientedArea a b c < 0) (dSide : 0 < orientedArea a b d)
    (aSide : 0 < orientedArea c d a) (bSide : orientedArea c d b < 0) :
    ∃ point : ℝ × ℝ, first.RealContains point ∧ second.RealContains point := by
  obtain ⟨point,firstInterior,secondInterior⟩ := real_interior_contact_of_opposite_sides
    firstStart firstEnd secondStart secondEnd cSide dSide aSide bSide
  exact ⟨point,realInteriorContains_implies_realContains firstInterior,
    realInteriorContains_implies_realContains secondInterior⟩

end LeanTrominoes.GridSegment
