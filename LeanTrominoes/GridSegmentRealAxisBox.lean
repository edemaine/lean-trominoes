/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GridSegmentRealLineCharacterization

/-! # The bounding box of an orthogonal segment is its closed real image -/
namespace LeanTrominoes.GridSegment

theorem realContains_of_axis_box {segment : GridSegment} {point : ℝ × ℝ}
    (axis : segment.IsAxisAligned) (bounds : segment.RealBoxContains point) : segment.RealContains point := by
  apply (realContains_iff_box_and_line segment point).mpr
  refine ⟨bounds,?_⟩
  rcases axis with horizontal | vertical
  · have sameY : segment.finish.2 = segment.start.2 := horizontal.1.symm
    have yBounds := bounds.2.2
    simp only [sameY,min_self,max_self] at yBounds
    have yEq : point.2 = (segment.start.2 : ℝ) := le_antisymm yBounds.2 yBounds.1
    simp [RealLineContains,sameY,yEq]
  · have sameX : segment.finish.1 = segment.start.1 := vertical.1.symm
    have xBounds := And.intro bounds.1 bounds.2.1
    simp only [sameX,min_self,max_self] at xBounds
    have xEq : point.1 = (segment.start.1 : ℝ) := le_antisymm xBounds.2 xBounds.1
    simp [RealLineContains,sameX,xEq]

theorem realContains_iff_axis_box {segment : GridSegment} (axis : segment.IsAxisAligned) (point : ℝ × ℝ) :
    segment.RealContains point ↔ segment.RealBoxContains point :=
  ⟨realBoxContains_of_realContains,realContains_of_axis_box axis⟩

end LeanTrominoes.GridSegment
