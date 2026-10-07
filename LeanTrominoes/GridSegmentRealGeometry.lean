/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawing
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! # Straight grid segments as subsets of the real plane

Unlike the axis-only raster predicates, these predicates include diagonal
segments. They support the unrestricted-degree fans in Theorem 2.1 and the
input polygonal drawing in Theorem 2.2.
-/
namespace LeanTrominoes.GridSegment

def RealContains (segment : GridSegment) (point : ℝ × ℝ) : Prop :=
  ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
    point.1 = segment.start.1 + t*(segment.finish.1-segment.start.1) ∧
    point.2 = segment.start.2 + t*(segment.finish.2-segment.start.2)

def RealInteriorContains (segment : GridSegment) (point : ℝ × ℝ) : Prop :=
  ∃ t : ℝ, 0 < t ∧ t < 1 ∧
    point.1 = segment.start.1 + t*(segment.finish.1-segment.start.1) ∧
    point.2 = segment.start.2 + t*(segment.finish.2-segment.start.2)

theorem realContains_start (segment : GridSegment) :
    segment.RealContains ((segment.start.1 : ℝ),(segment.start.2 : ℝ)) := by
  exact ⟨0,by norm_num,by norm_num,by ring,by ring⟩

theorem realContains_finish (segment : GridSegment) :
    segment.RealContains ((segment.finish.1 : ℝ),(segment.finish.2 : ℝ)) := by
  exact ⟨1,by norm_num,by norm_num,by ring,by ring⟩

theorem realContains_translate (segment : GridSegment) (offset : Cell) (point : ℝ × ℝ) :
    (segment.translate offset).RealContains (offset.1+point.1,offset.2+point.2) ↔
      segment.RealContains point := by
  unfold RealContains translate
  simp only [Cell.add,Int.cast_add]
  constructor <;> rintro ⟨t,lo,hi,hx,hy⟩ <;> refine ⟨t,lo,hi,?_,?_⟩ <;> nlinarith

theorem realInteriorContains_implies_realContains {segment : GridSegment} {point : ℝ × ℝ}
    (member : segment.RealInteriorContains point) : segment.RealContains point := by
  obtain ⟨t,lo,hi,hx,hy⟩ := member
  exact ⟨t,lo.le,hi.le,hx,hy⟩

/-- Distinct straight fan rays to a common port row meet only at their center. -/
theorem straight_fan_meet_only_at_center (center firstPort secondPort : Int)
    (different : firstPort ≠ secondPort) (point : ℝ × ℝ)
    (first : (⟨(center,2),(firstPort,3)⟩ : GridSegment).RealContains point)
    (second : (⟨(center,2),(secondPort,3)⟩ : GridSegment).RealContains point) :
    point = ((center : ℝ),2) := by
  obtain ⟨t,_,_,hx,hy⟩ := first
  obtain ⟨u,_,_,kx,ky⟩ := second
  have equal : t = u := by norm_num at hy ky; linarith
  subst u
  have product : t*((firstPort : ℝ)-(secondPort : ℝ)) = 0 := by nlinarith [hx,kx]
  have nonzero : (firstPort : ℝ)-(secondPort : ℝ) ≠ 0 := by
    intro zero
    exact different (by exact_mod_cast (sub_eq_zero.mp zero))
  have tzero := (mul_eq_zero.mp product).resolve_right nonzero
  subst t
  apply Prod.ext
  · simpa using hx
  · simpa using hy

theorem straight_fan_vertical_band (center port : Int) (point : ℝ × ℝ)
    (member : (⟨(center,2),(port,3)⟩ : GridSegment).RealContains point) :
    2 ≤ point.2 ∧ point.2 ≤ 3 := by
  obtain ⟨t,lo,hi,_,hy⟩ := member
  norm_num at hy
  constructor <;> linarith

end LeanTrominoes.GridSegment
