/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GridSegmentRealGeometry

/-! # Integer separating lines survive bounded endpoint perturbations -/
namespace LeanTrominoes.GridSegment

def linearForm (normal point : Cell) : Int := normal.1*point.1+normal.2*point.2
def realLinearForm (normal : Cell) (point : ℝ × ℝ) : ℝ := normal.1*point.1+normal.2*point.2

def StrictlySeparated (normal : Cell) (first second : GridSegment) : Prop :=
  linearForm normal first.start<linearForm normal second.start ∧
  linearForm normal first.start<linearForm normal second.finish ∧
  linearForm normal first.finish<linearForm normal second.start ∧
  linearForm normal first.finish<linearForm normal second.finish

private theorem convex_scalar_bounds (first last : Int) (t value : ℝ)
    (lo : 0≤t) (hi : t≤1) (equation : value=first+t*(last-first)) :
    (min first last : Int)≤value ∧ value≤(max first last : Int) := by
  rcases le_total first last with increasing | decreasing
  · rw [min_eq_left increasing,max_eq_right increasing]
    have positive : (0:ℝ)≤(last:ℝ)-first := by exact_mod_cast sub_nonneg.mpr increasing
    constructor <;> nlinarith [mul_nonneg lo positive,mul_nonneg (by linarith : 0≤1-t) positive]
  · rw [min_eq_right decreasing,max_eq_left decreasing]
    have positive : (0:ℝ)≤(first:ℝ)-last := by exact_mod_cast sub_nonneg.mpr decreasing
    constructor <;> nlinarith [mul_nonneg lo positive,mul_nonneg (by linarith : 0≤1-t) positive]

theorem realLinearForm_bounds {s : GridSegment} {p : ℝ × ℝ} (normal : Cell)
    (member : s.RealContains p) :
    (min (linearForm normal s.start) (linearForm normal s.finish) : Int)≤realLinearForm normal p ∧
      realLinearForm normal p≤(max (linearForm normal s.start) (linearForm normal s.finish) : Int) := by
  obtain ⟨t,lo,hi,x,y⟩ := member
  apply convex_scalar_bounds _ _ t _ lo hi
  simp only [realLinearForm,linearForm,Int.cast_add,Int.cast_mul]
  rw [x,y]
  ring

theorem StrictlySeparated.no_common_point {normal : Cell} {first second : GridSegment}
    (separated : StrictlySeparated normal first second) (p : ℝ × ℝ)
    (firstMember : first.RealContains p) : ¬ second.RealContains p := by
  intro secondMember
  have firstBounds := realLinearForm_bounds normal firstMember
  have secondBounds := realLinearForm_bounds normal secondMember
  have gap : max (linearForm normal first.start) (linearForm normal first.finish)<
      min (linearForm normal second.start) (linearForm normal second.finish) :=
    max_lt_iff.mpr ⟨lt_min separated.1 separated.2.1,lt_min separated.2.2.1 separated.2.2.2⟩
  have strict : (max (linearForm normal first.start) (linearForm normal first.finish) : Int) <
      (min (linearForm normal second.start) (linearForm normal second.finish) : Int) := gap
  have realStrict : ((max (linearForm normal first.start) (linearForm normal first.finish) : Int) : ℝ) <
      ((min (linearForm normal second.start) (linearForm normal second.finish) : Int) : ℝ) := by exact_mod_cast strict
  linarith [firstBounds.2,secondBounds.1]

def PointPerturbation (factor : Int) (original output : Cell) : Prop :=
  |output.1-factor*original.1|≤1 ∧ |output.2-factor*original.2|≤1

def EndpointPerturbation (factor : Int) (original output : GridSegment) : Prop :=
  PointPerturbation factor original.start output.start ∧ PointPerturbation factor original.finish output.finish

theorem linearForm_perturbation_bound {factor bound : Int} (nonnegative : 0≤bound)
    (normal original output : Cell) (normalBounds : |normal.1|≤bound ∧ |normal.2|≤bound)
    (perturbed : PointPerturbation factor original output) :
    |linearForm normal output-factor*linearForm normal original|≤2*bound := by
  calc
    _ = |normal.1*(output.1-factor*original.1)+normal.2*(output.2-factor*original.2)| := by
      congr 1
      unfold linearForm
      ring
    _ ≤ |normal.1*(output.1-factor*original.1)| + |normal.2*(output.2-factor*original.2)| := abs_add_le _ _
    _ = |normal.1| * |output.1-factor*original.1| + |normal.2| * |output.2-factor*original.2| := by rw [abs_mul,abs_mul]
    _ ≤ bound*1+bound*1 := add_le_add
      (mul_le_mul normalBounds.1 perturbed.1 (abs_nonneg _) nonnegative)
      (mul_le_mul normalBounds.2 perturbed.2 (abs_nonneg _) nonnegative)
    _ = _ := by ring

theorem linearForm_lt_of_perturbation {factor bound : Int} (nonnegative : 0≤bound) (spacing : 4*bound<factor)
    (normal first second firstOutput secondOutput : Cell) (normalBounds : |normal.1|≤bound ∧ |normal.2|≤bound)
    (firstPerturbed : PointPerturbation factor first firstOutput)
    (secondPerturbed : PointPerturbation factor second secondOutput)
    (ordered : linearForm normal first<linearForm normal second) :
    linearForm normal firstOutput<linearForm normal secondOutput := by
  have firstBounds := abs_le.mp (linearForm_perturbation_bound nonnegative normal first firstOutput normalBounds firstPerturbed)
  have secondBounds := abs_le.mp (linearForm_perturbation_bound nonnegative normal second secondOutput normalBounds secondPerturbed)
  have gap : linearForm normal first+1≤linearForm normal second := by omega
  have scaled := mul_le_mul_of_nonneg_left gap (show 0≤factor by omega)
  nlinarith

theorem StrictlySeparated.perturb {factor bound : Int} (nonnegative : 0≤bound) (spacing : 4*bound<factor)
    {normal : Cell} {first second firstOutput secondOutput : GridSegment}
    (separated : StrictlySeparated normal first second) (normalBounds : |normal.1|≤bound ∧ |normal.2|≤bound)
    (firstPerturbed : EndpointPerturbation factor first firstOutput)
    (secondPerturbed : EndpointPerturbation factor second secondOutput) :
    StrictlySeparated normal firstOutput secondOutput :=
  ⟨linearForm_lt_of_perturbation nonnegative spacing _ _ _ _ _ normalBounds firstPerturbed.1 secondPerturbed.1 separated.1,
    linearForm_lt_of_perturbation nonnegative spacing _ _ _ _ _ normalBounds firstPerturbed.1 secondPerturbed.2 separated.2.1,
    linearForm_lt_of_perturbation nonnegative spacing _ _ _ _ _ normalBounds firstPerturbed.2 secondPerturbed.1 separated.2.2.1,
    linearForm_lt_of_perturbation nonnegative spacing _ _ _ _ _ normalBounds firstPerturbed.2 secondPerturbed.2 separated.2.2.2⟩

end LeanTrominoes.GridSegment
