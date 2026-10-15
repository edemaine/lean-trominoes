/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Common.Geometry.GridSegmentRealGeometry

/-! # A rational shift that avoids simultaneous horizontal and vertical seams

After scaling by `(B+1)^2` and translating by `(1,B+1)`, a nonconstant
integer segment whose coordinate differences are at most `B` misses every
point of the old integer grid. In particular it cannot pass through a corner
of a periodically translated fundamental square.
-/
namespace LeanTrominoes.PeriodicGridDrawing.SeamShift

def factor (bound : Int) : Int := (bound+1)^2
def point (bound : Int) (p : Cell) : Cell :=
  (factor bound*p.1+1,factor bound*p.2+(bound+1))
def segment (bound : Int) (s : GridSegment) : GridSegment := ⟨point bound s.start,point bound s.finish⟩

theorem coefficient_nonzero {bound dx dy : Int} (positive : 0<bound)
    (_xBounds : -bound≤dx ∧ dx≤bound) (yBounds : -bound≤dy ∧ dy≤bound)
    (nonzero : dx≠0 ∨ dy≠0) : (bound+1)*dx-dy≠0 := by
  intro zero
  by_cases xZero : dx=0
  · have yZero : dy=0 := by simp [xZero] at zero; omega
    simp [xZero,yZero] at nonzero
  · have sides : dx≤-1 ∨ 1≤dx := by omega
    rcases sides with negative | positiveX <;> nlinarith

theorem coefficient_bounds {bound dx dy : Int} (positive : 0<bound)
    (xBounds : -bound≤dx ∧ dx≤bound) (yBounds : -bound≤dy ∧ dy≤bound) :
    -factor bound<(bound+1)*dx-dy ∧ (bound+1)*dx-dy<factor bound := by
  have left := mul_le_mul_of_nonneg_left xBounds.1 (show 0≤bound+1 by omega)
  have right := mul_le_mul_of_nonneg_left xBounds.2 (show 0≤bound+1 by omega)
  unfold factor
  constructor <;> nlinarith

theorem coefficient_not_multiple {bound dx dy : Int} (positive : 0<bound)
    (xBounds : -bound≤dx ∧ dx≤bound) (yBounds : -bound≤dy ∧ dy≤bound)
    (nonzero : dx≠0 ∨ dy≠0) (multiple : Int) :
    factor bound*multiple≠(bound+1)*dx-dy := by
  intro equal
  have bounds := coefficient_bounds positive xBounds yBounds
  have factorPositive : 0<factor bound := by unfold factor; positivity
  have multipleZero : multiple=0 := by
    by_contra different
    have sides : multiple≤-1 ∨ 1≤multiple := by omega
    rcases sides with negative | positiveMultiple
    · have h := mul_le_mul_of_nonneg_left negative factorPositive.le
      nlinarith
    · have h := mul_le_mul_of_nonneg_left positiveMultiple factorPositive.le
      nlinarith
  rw [multipleZero,mul_zero] at equal
  exact coefficient_nonzero positive xBounds yBounds nonzero equal.symm

theorem realContains_determinant {s : GridSegment} {p : ℝ × ℝ} (member : s.RealContains p) :
    (p.1-s.start.1)*(s.finish.2-s.start.2)=(p.2-s.start.2)*(s.finish.1-s.start.1) := by
  obtain ⟨t,_,_,x,y⟩ := member
  rw [x,y]
  ring

theorem avoids_scaled_grid {bound : Int} (positive : 0<bound) (s : GridSegment)
    (xBounds : -bound≤s.finish.1-s.start.1 ∧ s.finish.1-s.start.1≤bound)
    (yBounds : -bound≤s.finish.2-s.start.2 ∧ s.finish.2-s.start.2≤bound)
    (nonconstant : s.start≠s.finish) (corner : Cell) :
    ¬ (segment bound s).RealContains ((factor bound*corner.1 : Int),(factor bound*corner.2 : Int)) := by
  intro member
  have det := realContains_determinant member
  have intDet :
      (factor bound*corner.1-(factor bound*s.start.1+1)) *
          (factor bound*s.finish.2+(bound+1)-(factor bound*s.start.2+(bound+1))) =
      (factor bound*corner.2-(factor bound*s.start.2+(bound+1))) *
          (factor bound*s.finish.1+1-(factor bound*s.start.1+1)) := by
    simp only [segment,point] at det
    exact_mod_cast det
  have factored : factor bound *
      (factor bound*((corner.1-s.start.1)*(s.finish.2-s.start.2)-
        (corner.2-s.start.2)*(s.finish.1-s.start.1)) +
        ((bound+1)*(s.finish.1-s.start.1)-(s.finish.2-s.start.2)))=0 := by
    convert sub_eq_zero.mpr intDet using 1
    ring
  have factorNonzero : factor bound≠0 := by unfold factor; positivity
  have inner := (mul_eq_zero.mp factored).resolve_left factorNonzero
  have equation : factor bound *
      ((corner.2-s.start.2)*(s.finish.1-s.start.1)-
        (corner.1-s.start.1)*(s.finish.2-s.start.2)) =
      (bound+1)*(s.finish.1-s.start.1)-(s.finish.2-s.start.2) := by linear_combination -inner
  have nonzero : s.finish.1-s.start.1≠0 ∨ s.finish.2-s.start.2≠0 := by
    by_contra zero
    simp only [not_or,not_not,sub_eq_zero] at zero
    exact nonconstant (Prod.ext zero.1.symm zero.2.symm)
  exact coefficient_not_multiple positive xBounds yBounds nonzero _ equation

end LeanTrominoes.PeriodicGridDrawing.SeamShift
