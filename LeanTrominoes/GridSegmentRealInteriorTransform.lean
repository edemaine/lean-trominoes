/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GridPolylineRealAlgebra

/-! # Reversal and translation preserve proper segment contacts -/
namespace LeanTrominoes.GridSegment

theorem realInteriorContains_reverse (segment : GridSegment) (point : ℝ × ℝ) :
    segment.reverse.RealInteriorContains point ↔ segment.RealInteriorContains point := by
  constructor
  all_goals
    rintro ⟨t,lo,hi,hx,hy⟩
    refine ⟨1-t,by linarith,by linarith,?_,?_⟩
    all_goals simp only [reverse] at hx hy ⊢ <;> nlinarith

theorem realInteriorContains_translate (segment : GridSegment) (offset : Cell) (point : ℝ × ℝ) :
    (segment.translate offset).RealInteriorContains
      (point.1+(offset.1 : ℝ),point.2+(offset.2 : ℝ)) ↔ segment.RealInteriorContains point := by
  simp only [RealInteriorContains,translate,Cell.add,Int.cast_add,Prod.fst,Prod.snd]
  constructor
  all_goals
    rintro ⟨t,lo,hi,hx,hy⟩
    refine ⟨t,lo,hi,?_,?_⟩ <;> linarith

end LeanTrominoes.GridSegment
