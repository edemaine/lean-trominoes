/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRealGeometry

/-! # A proper contact of a nondegenerate segment is away from both endpoints -/
namespace LeanTrominoes.GridSegment

theorem realInteriorContains_not_endpoints {segment : GridSegment} {point : ℝ × ℝ}
    (nondegenerate : segment.start ≠ segment.finish) (contains : segment.RealInteriorContains point) :
    point ≠ realCell segment.start ∧ point ≠ realCell segment.finish := by
  obtain ⟨t,lo,hi,hx,hy⟩ := contains
  constructor
  · intro equal
    have ex := congrArg Prod.fst equal
    have ey := congrArg Prod.snd equal
    simp only [realCell,Prod.fst,Prod.snd] at ex ey
    have xzero : t*((segment.finish.1 : ℝ)-segment.start.1) = 0 := by linarith
    have yzero : t*((segment.finish.2 : ℝ)-segment.start.2) = 0 := by linarith
    have xeq := sub_eq_zero.mp ((mul_eq_zero.mp xzero).resolve_left lo.ne')
    have yeq := sub_eq_zero.mp ((mul_eq_zero.mp yzero).resolve_left lo.ne')
    exact nondegenerate (Prod.ext (by exact_mod_cast xeq.symm) (by exact_mod_cast yeq.symm))
  · intro equal
    have ex := congrArg Prod.fst equal
    have ey := congrArg Prod.snd equal
    simp only [realCell,Prod.fst,Prod.snd] at ex ey
    have xzero : (1-t)*((segment.finish.1 : ℝ)-segment.start.1) = 0 := by nlinarith
    have yzero : (1-t)*((segment.finish.2 : ℝ)-segment.start.2) = 0 := by nlinarith
    have scalarNonzero : 1-t ≠ 0 := by linarith
    have xeq := sub_eq_zero.mp ((mul_eq_zero.mp xzero).resolve_left scalarNonzero)
    have yeq := sub_eq_zero.mp ((mul_eq_zero.mp yzero).resolve_left scalarNonzero)
    exact nondegenerate (Prod.ext (by exact_mod_cast xeq.symm) (by exact_mod_cast yeq.symm))

end LeanTrominoes.GridSegment
