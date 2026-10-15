/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Common.Geometry.GridSegmentRealTubeTranslation
import LeanTrominoes.Common.Geometry.GridPolylineRealAlgebra

/-! # Segment boxes under reversal and scaled translation -/
namespace LeanTrominoes.GridSegment

theorem RealBoxContains.reverse {segment : GridSegment} {point : ℝ × ℝ}
    (contains : segment.RealBoxContains point) : segment.reverse.RealBoxContains point := by
  simpa only [RealBoxContains,GridSegment.reverse,min_comm,max_comm] using contains

theorem RealBoxContains.translate {segment : GridSegment} {point : ℝ × ℝ}
    (contains : segment.RealBoxContains point) (offset : Cell) :
    (segment.translate offset).RealBoxContains (offset.1+point.1,offset.2+point.2) := by
  simp only [RealBoxContains,GridSegment.translate,Cell.add,min_add_add_left,max_add_add_left,Int.cast_add]
  exact ⟨by linarith [contains.1],by linarith [contains.2.1],by linarith [contains.2.2.1],by linarith [contains.2.2.2]⟩

theorem RealBoxContains.translate_scaled {segment : GridSegment} {factor : Int} {point : ℝ × ℝ}
    (contains : (segment.scale factor).RealBoxContains point) (offset : Cell) :
    ((segment.translate offset).scale factor).RealBoxContains
      ((factor : ℝ)*offset.1+point.1,(factor : ℝ)*offset.2+point.2) := by
  rw [segment_translate_scale]
  simpa only [Cell.scale,Int.cast_mul] using contains.translate (Cell.scale factor offset)

end LeanTrominoes.GridSegment
