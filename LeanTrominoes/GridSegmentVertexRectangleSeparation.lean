/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GridSegmentRealIntersection
import LeanTrominoes.PeriodicGridDrawingScaling

/-! # Separating vertex rectangles from noncollinear grid segments

A nonzero determinant of integer vectors has absolute value at least one.
After refinement this excludes the small vertex rectangles used in the
orthogonalization construction, even for diagonal input segments.
-/
namespace LeanTrominoes.GridSegment

def vertexDeterminant (segment : GridSegment) (vertex : Cell) : Int :=
  (segment.start.1-vertex.1)*(segment.finish.2-segment.start.2)-
    (segment.start.2-vertex.2)*(segment.finish.1-segment.start.1)

theorem noncollinear_rectangle_avoids_segment {segment : GridSegment} {vertex : Cell}
    {grid factor : Int} (gridNonnegative : 0 ≤ grid) (spacing : 30*grid < factor)
    (horizontalBound : |segment.finish.1-segment.start.1| ≤ 2*grid)
    (verticalBound : |segment.finish.2-segment.start.2| ≤ 2*grid)
    (noncollinear : segment.vertexDeterminant vertex ≠ 0) {point : ℝ × ℝ}
    (horizontalNear : |point.1-(factor : ℝ)*vertex.1| ≤ 5)
    (verticalNear : |point.2-(factor : ℝ)*vertex.2| ≤ 10) :
    ¬ (segment.scale factor).RealContains point := by
  intro member
  obtain ⟨t,_,_,hx,hy⟩ := member
  simp only [scale,Cell.scale,Int.cast_mul] at hx hy
  let dx : ℝ := (segment.finish.1 : ℝ)-segment.start.1
  let dy : ℝ := (segment.finish.2 : ℝ)-segment.start.2
  let rx : ℝ := point.1-(factor : ℝ)*vertex.1
  let ry : ℝ := point.2-(factor : ℝ)*vertex.2
  have detEq : (factor : ℝ)*(segment.vertexDeterminant vertex : ℝ) = rx*dy-ry*dx := by
    simp only [vertexDeterminant,Int.cast_sub,Int.cast_mul]
    dsimp [dx,dy,rx,ry]
    rw [hx,hy]
    ring
  have dxBound : |dx| ≤ 2*(grid : ℝ) := by
    dsimp [dx]
    exact_mod_cast horizontalBound
  have dyBound : |dy| ≤ 2*(grid : ℝ) := by
    dsimp [dy]
    exact_mod_cast verticalBound
  have upper : |rx*dy-ry*dx| ≤ 30*(grid : ℝ) := calc
    _ ≤ |rx*dy|+|ry*dx| := abs_sub _ _
    _ = |rx| * |dy| + |ry| * |dx| := by rw [abs_mul,abs_mul]
    _ ≤ 5*(2*(grid : ℝ))+10*(2*(grid : ℝ)) :=
      add_le_add (mul_le_mul horizontalNear dyBound (abs_nonneg _) (by norm_num))
        (mul_le_mul verticalNear dxBound (abs_nonneg _) (by norm_num))
    _ = _ := by ring
  have determinantLower : (1 : ℝ) ≤ |(segment.vertexDeterminant vertex : ℝ)| := by
    have positive : 0 < |segment.vertexDeterminant vertex| := abs_pos.mpr noncollinear
    have integral : 1 ≤ |segment.vertexDeterminant vertex| := by omega
    exact_mod_cast integral
  have factorPositive : (0 : ℝ) < factor := by
    have positive : 0 < factor := by omega
    exact_mod_cast positive
  have strict : 30*(grid : ℝ) < factor := by exact_mod_cast spacing
  rw [← detEq,abs_mul,abs_of_pos factorPositive] at upper
  nlinarith

end LeanTrominoes.GridSegment
