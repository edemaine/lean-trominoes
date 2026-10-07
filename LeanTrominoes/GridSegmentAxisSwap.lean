/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GridSegmentRealGeometry

/-! # Swapping coordinate axes preserves straight-segment containment -/
namespace LeanTrominoes.GridSegment

def swapAxes (segment : GridSegment) : GridSegment := ⟨segment.start.swap,segment.finish.swap⟩

theorem swapAxes_translate (segment : GridSegment) (offset : Cell) :
    (segment.translate offset).swapAxes = segment.swapAxes.translate offset.swap := by
  cases segment
  rfl

theorem realContains_swapAxes (segment : GridSegment) (point : ℝ × ℝ) :
    segment.swapAxes.RealContains point.swap ↔ segment.RealContains point := by
  simp only [RealContains,swapAxes,Prod.swap,Prod.fst,Prod.snd]
  constructor <;> rintro ⟨t,lo,hi,first,second⟩ <;> exact ⟨t,lo,hi,second,first⟩

end LeanTrominoes.GridSegment
