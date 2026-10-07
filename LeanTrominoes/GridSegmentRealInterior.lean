/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GridSegmentRealGeometry

/-! # A closed segment contact away from its endpoints is interior -/
namespace LeanTrominoes.GridSegment

theorem realInteriorContains_of_realContains_of_not_endpoints {segment : GridSegment} {point : ℝ × ℝ}
    (contains : segment.RealContains point)
    (notStart : point ≠ ((segment.start.1 : ℝ),(segment.start.2 : ℝ)))
    (notFinish : point ≠ ((segment.finish.1 : ℝ),(segment.finish.2 : ℝ))) :
    segment.RealInteriorContains point := by
  obtain ⟨t,lo,hi,hx,hy⟩ := contains
  refine ⟨t,?_,?_,hx,hy⟩
  · by_contra bad
    have zero : t = 0 := by linarith
    apply notStart
    apply Prod.ext <;> simp_all
  · by_contra bad
    have one : t = 1 := by linarith
    apply notFinish
    apply Prod.ext <;> simp_all

end LeanTrominoes.GridSegment
