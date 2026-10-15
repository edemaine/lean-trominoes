/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Common.Geometry.GridSegmentRealLineCharacterization
import LeanTrominoes.Common.Geometry.GridSegmentVertexRectangleSeparation

/-! # Vertex rectangles also avoid collinear nonincident segments -/
namespace LeanTrominoes.GridSegment

private theorem center_in_integer_interval {lower upper center factor : Int} {point : ℝ}
    (spacing : 10 < factor)
    (bounds : (factor : ℝ)*lower ≤ point ∧ point ≤ (factor : ℝ)*upper)
    (near : |point-(factor : ℝ)*center| ≤ 10) : lower ≤ center ∧ center ≤ upper := by
  have positive : (0 : ℝ) < factor := by exact_mod_cast (by omega : 0 < factor)
  have strict : (10 : ℝ) < factor := by exact_mod_cast spacing
  have absolute := abs_le.mp near
  constructor
  · by_contra outside
    have gap : (center : ℝ)+1 ≤ lower := by exact_mod_cast (by omega : center+1 ≤ lower)
    nlinarith [bounds.1,absolute.2]
  · by_contra outside
    have gap : (upper : ℝ)+1 ≤ center := by exact_mod_cast (by omega : upper+1 ≤ center)
    nlinarith [bounds.2,absolute.1]

theorem collinear_rectangle_avoids_segment {segment : GridSegment} {vertex : Cell}
    {factor : Int} (spacing : 10 < factor)
    (collinear : segment.vertexDeterminant vertex = 0)
    (nonincident : ¬ segment.RealContains ((vertex.1 : ℝ),(vertex.2 : ℝ)))
    {point : ℝ × ℝ}
    (horizontalNear : |point.1-(factor : ℝ)*vertex.1| ≤ 5)
    (verticalNear : |point.2-(factor : ℝ)*vertex.2| ≤ 10) :
    ¬ (segment.scale factor).RealContains point := by
  intro member
  have factorPositive : (0 : ℝ) < factor := by exact_mod_cast (by omega : 0 < factor)
  have bounds := realBoxContains_of_realContains member
  simp only [RealBoxContains,scale,Cell.scale,Int.cast_min,Int.cast_max,Int.cast_mul] at bounds
  rw [← mul_min_of_nonneg _ _ factorPositive.le,← mul_max_of_nonneg _ _ factorPositive.le,
    ← mul_min_of_nonneg _ _ factorPositive.le,← mul_max_of_nonneg _ _ factorPositive.le] at bounds
  have xb : min segment.start.1 segment.finish.1 ≤ vertex.1 ∧
      vertex.1 ≤ max segment.start.1 segment.finish.1 :=
    center_in_integer_interval spacing (by
      simpa only [Int.cast_min,Int.cast_max] using (And.intro bounds.1 bounds.2.1))
      (horizontalNear.trans (by norm_num))
  have yb : min segment.start.2 segment.finish.2 ≤ vertex.2 ∧
      vertex.2 ≤ max segment.start.2 segment.finish.2 :=
    center_in_integer_interval spacing (by
      simpa only [Int.cast_min,Int.cast_max] using (And.intro bounds.2.2.1 bounds.2.2.2)) verticalNear
  have line : segment.RealLineContains ((vertex.1 : ℝ),(vertex.2 : ℝ)) := by
    have zero : (segment.vertexDeterminant vertex : ℝ) = 0 := by exact_mod_cast collinear
    simp only [vertexDeterminant,Int.cast_sub,Int.cast_mul] at zero
    unfold RealLineContains
    dsimp only [Prod.fst,Prod.snd]
    linear_combination -zero
  apply nonincident
  apply (realContains_iff_box_and_line _ _).mpr
  refine ⟨?_,line⟩
  change (_ : ℝ) ≤ (vertex.1 : ℝ) ∧ (vertex.1 : ℝ) ≤ (_ : ℝ) ∧
    (_ : ℝ) ≤ (vertex.2 : ℝ) ∧ (vertex.2 : ℝ) ≤ (_ : ℝ)
  exact ⟨by exact_mod_cast xb.1,by exact_mod_cast xb.2,
    by exact_mod_cast yb.1,by exact_mod_cast yb.2⟩

/-- Every nonincident input segment misses the vertex rectangle, including
diagonal, collinear, and degenerate segments. -/
theorem vertex_rectangle_avoids_nonincident_segment {segment : GridSegment} {vertex : Cell}
    {grid factor : Int} (gridNonnegative : 0 ≤ grid) (spacing : 30*grid+10 < factor)
    (horizontalBound : |segment.finish.1-segment.start.1| ≤ 2*grid)
    (verticalBound : |segment.finish.2-segment.start.2| ≤ 2*grid)
    (nonincident : ¬ segment.RealContains ((vertex.1 : ℝ),(vertex.2 : ℝ)))
    {point : ℝ × ℝ}
    (horizontalNear : |point.1-(factor : ℝ)*vertex.1| ≤ 5)
    (verticalNear : |point.2-(factor : ℝ)*vertex.2| ≤ 10) :
    ¬ (segment.scale factor).RealContains point := by
  by_cases collinear : segment.vertexDeterminant vertex = 0
  · exact collinear_rectangle_avoids_segment (by omega) collinear nonincident horizontalNear verticalNear
  · exact noncollinear_rectangle_avoids_segment gridNonnegative (by omega)
      horizontalBound verticalBound collinear horizontalNear verticalNear

end LeanTrominoes.GridSegment
