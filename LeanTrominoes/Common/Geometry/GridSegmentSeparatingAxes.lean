/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Common.Geometry.GridSegmentIntegerSeparator

/-! # Intersection and integer separating axes for arbitrary grid segments -/
namespace LeanTrominoes.GridSegment

def cross (a b : Cell) : Int := a.1*b.2-a.2*b.1
def direction (s : GridSegment) : Cell := (s.finish.1-s.start.1,s.finish.2-s.start.2)
def side (s : GridSegment) (p : Cell) : Int := cross s.direction (p.1-s.start.1,p.2-s.start.2)
def normal (s : GridSegment) : Cell := (-s.direction.2,s.direction.1)

theorem side_eq_linearForm (s : GridSegment) (p : Cell) :
    s.side p=linearForm s.normal p-linearForm s.normal s.start := by
  unfold side cross normal direction linearForm
  ring

theorem normal_endpoints_eq (s : GridSegment) : linearForm s.normal s.start=linearForm s.normal s.finish := by
  unfold normal direction linearForm
  ring

theorem sides_difference (first second : GridSegment) :
    first.side second.finish-first.side second.start=cross first.direction second.direction := by
  unfold side cross direction
  ring

theorem cross_swap (first second : Cell) : cross first second = -cross second first := by unfold cross; ring

theorem intersects_of_straddling {first second : GridSegment}
    (positive : 0<cross first.direction second.direction)
    (firstStart : first.side second.start≤0) (firstFinish : 0≤first.side second.finish)
    (secondStart : 0≤second.side first.start) (secondFinish : second.side first.finish≤0) :
    ∃ p : ℝ × ℝ, first.RealContains p ∧ second.RealContains p := by
  let determinant := cross first.direction second.direction
  have determinantPositive : (0:ℝ)<(determinant:ℝ) := by exact_mod_cast positive
  have determinantNonzero : (determinant:ℝ)≠0 := ne_of_gt determinantPositive
  have firstDifference := sides_difference first second
  have secondDifference := sides_difference second first
  rw [cross_swap second.direction first.direction] at secondDifference
  let t : ℝ := (second.side first.start:ℝ)/(determinant:ℝ)
  let u : ℝ := -(first.side second.start:ℝ)/(determinant:ℝ)
  have tBounds : 0≤t ∧ t≤1 := by
    have lo : (0:ℝ)≤(second.side first.start:ℝ) := by exact_mod_cast secondStart
    have hi : (second.side first.start:ℝ)≤(determinant:ℝ) := by
      exact_mod_cast (show second.side first.start≤determinant by dsimp [determinant]; omega)
    exact ⟨div_nonneg lo determinantPositive.le,(div_le_one determinantPositive).mpr hi⟩
  have uBounds : 0≤u ∧ u≤1 := by
    have lo : (0:ℝ)≤-(first.side second.start:ℝ) := by exact_mod_cast (show 0≤-first.side second.start by omega)
    have hi : -(first.side second.start:ℝ)≤(determinant:ℝ) := by
      exact_mod_cast (show -first.side second.start≤determinant by dsimp [determinant]; omega)
    exact ⟨div_nonneg lo determinantPositive.le,(div_le_one determinantPositive).mpr hi⟩
  have x : (first.start.1:ℝ)+t*(first.direction.1:ℝ)=
      (second.start.1:ℝ)+u*(second.direction.1:ℝ) := by
    dsimp [t,u]
    field_simp [determinantNonzero]
    simp only [determinant,side,cross,direction,Int.cast_sub,Int.cast_mul]
    ring
  have y : (first.start.2:ℝ)+t*(first.direction.2:ℝ)=
      (second.start.2:ℝ)+u*(second.direction.2:ℝ) := by
    dsimp [t,u]
    field_simp [determinantNonzero]
    simp only [determinant,side,cross,direction,Int.cast_sub,Int.cast_mul]
    ring
  refine ⟨((first.start.1:ℝ)+t*(first.direction.1:ℝ),(first.start.2:ℝ)+t*(first.direction.2:ℝ)),
    ⟨t,tBounds.1,tBounds.2,?_,?_⟩,⟨u,uBounds.1,uBounds.2,?_,?_⟩⟩
  · simp [direction]
  · simp [direction]
  · simpa only [direction,Int.cast_sub] using x
  · simpa only [direction,Int.cast_sub] using y

theorem strictlySeparated_of_positive_sides {first second : GridSegment}
    (start : 0<first.side second.start) (finish : 0<first.side second.finish) :
    StrictlySeparated first.normal first second := by
  rw [side_eq_linearForm] at start finish
  have endpoints := normal_endpoints_eq first
  unfold StrictlySeparated
  omega

theorem strictlySeparated_of_negative_sides {first second : GridSegment}
    (start : first.side second.start<0) (finish : first.side second.finish<0) :
    StrictlySeparated (-first.normal.1,-first.normal.2) first second := by
  rw [side_eq_linearForm] at start finish
  have endpoints := normal_endpoints_eq first
  have negate (p : Cell) : linearForm (-first.normal.1,-first.normal.2) p= -linearForm first.normal p := by
    unfold linearForm
    ring
  unfold StrictlySeparated
  simp only [negate]
  omega

end LeanTrominoes.GridSegment
