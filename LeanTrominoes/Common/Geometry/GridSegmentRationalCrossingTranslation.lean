/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Common.Geometry.GridSegmentRationalVerticalCrossing

/-! # Exact crossing heights commute with integral translations -/
namespace LeanTrominoes.GridSegment

theorem crossesVerticalLine_translate (segment : GridSegment) (offset : Cell) (line : Int) :
    (segment.translate offset).CrossesVerticalLine (line+offset.1) ↔ segment.CrossesVerticalLine line := by
  simp [CrossesVerticalLine,translate,Cell.add]
  omega

theorem rationalLineHeight_translate (segment : GridSegment) (offset : Cell) (line : Int) :
    (segment.translate offset).rationalLineHeight (line+offset.1) = segment.rationalLineHeight line+(offset.2 : ℚ) := by
  simp only [rationalLineHeight,translate,Cell.add,Int.cast_add,Prod.fst,Prod.snd]
  ring

end LeanTrominoes.GridSegment
