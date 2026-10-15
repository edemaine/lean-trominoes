/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Common.Geometry.GridSegmentRealTube

/-! # Coordinate tube bounds in every translated periodic copy -/
namespace LeanTrominoes.GridSegment

theorem RealTubeContains.translate {segment : GridSegment} {radius : ℝ} {point : ℝ × ℝ}
    (contains : segment.RealTubeContains radius point) (offset : Cell) :
    (segment.translate offset).RealTubeContains radius (offset.1+point.1,offset.2+point.2) := by
  obtain ⟨original,originalContains,x,y⟩ := contains
  refine ⟨(offset.1+original.1,offset.2+original.2),(realContains_translate segment offset original).mpr originalContains,?_,?_⟩
  · simpa only [add_sub_add_left_eq_sub] using x
  · simpa only [add_sub_add_left_eq_sub] using y

theorem segment_translate_scale (segment : GridSegment) (offset : Cell) (factor : Int) :
    (segment.translate offset).scale factor = (segment.scale factor).translate (Cell.scale factor offset) := by
  cases segment
  unfold GridSegment.translate GridSegment.scale
  congr 1 <;> apply Prod.ext <;> simp only [Cell.add,Cell.scale] <;> ring

theorem RealTubeContains.translate_scaled {segment : GridSegment} {radius : ℝ} {point : ℝ × ℝ}
    {factor : Int} (contains : (segment.scale factor).RealTubeContains radius point) (offset : Cell) :
    ((segment.translate offset).scale factor).RealTubeContains radius
      ((factor : ℝ)*offset.1+point.1,(factor : ℝ)*offset.2+point.2) := by
  rw [segment_translate_scale]
  simpa only [Cell.scale,Int.cast_mul] using contains.translate (Cell.scale factor offset)

end LeanTrominoes.GridSegment
