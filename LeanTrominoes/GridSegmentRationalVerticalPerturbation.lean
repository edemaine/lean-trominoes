/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GridSegmentRationalSeamPerturbationTranslation

/-! # Exact intersections with rationally shifted vertical column cuts -/
namespace LeanTrominoes.GridSegment

def rationalHeightAt (segment : GridSegment) (coordinate : ℚ) : ℚ := segment.swapAxes.rationalAbscissaAt coordinate

theorem rationalHeightAt_int (segment : GridSegment) (line : Int) :
    segment.rationalHeightAt line = segment.rationalLineHeight line := rfl

theorem rationalHeightAt_add (segment : GridSegment) (coordinate epsilon : ℚ) :
    segment.rationalHeightAt (coordinate+epsilon) = segment.rationalHeightAt coordinate+epsilon*segment.rationalSlope := by
  unfold rationalHeightAt rationalAbscissaAt rationalSlope swapAxes
  dsimp only [Prod.swap,Prod.fst,Prod.snd]
  ring

theorem rationalHeightAt_translate (segment : GridSegment) (offset : Cell) (coordinate : ℚ) :
    (segment.translate offset).rationalHeightAt (coordinate+offset.1) = segment.rationalHeightAt coordinate+offset.2 := by
  unfold rationalHeightAt
  rw [swapAxes_translate]
  exact rationalAbscissaAt_translate segment.swapAxes offset.swap coordinate

theorem realInteriorContains_swapAxes (segment : GridSegment) (point : ℝ × ℝ) :
    segment.swapAxes.RealInteriorContains point.swap ↔ segment.RealInteriorContains point := by
  simp only [RealInteriorContains,swapAxes,Prod.swap,Prod.fst,Prod.snd]
  constructor <;> rintro ⟨t,lo,hi,first,second⟩ <;> exact ⟨t,lo,hi,second,first⟩

theorem rationalHeightAt_realInteriorContains {segment : GridSegment} {coordinate : ℚ}
    (between : ((segment.start.1 : ℚ) < coordinate ∧ coordinate < segment.finish.1) ∨
      ((segment.finish.1 : ℚ) < coordinate ∧ coordinate < segment.start.1)) :
    segment.RealInteriorContains ((coordinate : ℝ),(segment.rationalHeightAt coordinate : ℝ)) :=
  (realInteriorContains_swapAxes _ _).mp (rationalAbscissaAt_realInteriorContains (segment := segment.swapAxes) between)

theorem shifted_vertical_cut_realInteriorContains {segment : GridSegment} {line : Int} {epsilon : ℚ}
    (crosses : segment.CrossesVerticalLine line) (small : |epsilon| < 1) :
    segment.RealInteriorContains (((line : ℚ)+epsilon : ℝ),(segment.rationalHeightAt ((line : ℚ)+epsilon) : ℝ)) := by
  have lo := (abs_lt.mp small).1
  have hi := (abs_lt.mp small).2
  have between : ((segment.start.1 : ℚ) < (line : ℚ)+epsilon ∧ (line : ℚ)+epsilon < segment.finish.1) ∨
      ((segment.finish.1 : ℚ) < (line : ℚ)+epsilon ∧ (line : ℚ)+epsilon < segment.start.1) := by
    rcases crosses with forward | backward
    · have lower : (segment.start.1 : ℚ)+1 ≤ line := by exact_mod_cast (by omega : segment.start.1+1 ≤ line)
      have upper : (line : ℚ)+1 ≤ segment.finish.1 := by exact_mod_cast (by omega : line+1 ≤ segment.finish.1)
      exact Or.inl ⟨by linarith,by linarith⟩
    · have lower : (segment.finish.1 : ℚ)+1 ≤ line := by exact_mod_cast (by omega : segment.finish.1+1 ≤ line)
      have upper : (line : ℚ)+1 ≤ segment.start.1 := by exact_mod_cast (by omega : line+1 ≤ segment.start.1)
      exact Or.inr ⟨by linarith,by linarith⟩
  simpa only [Rat.cast_add,Rat.cast_intCast] using rationalHeightAt_realInteriorContains between

end LeanTrominoes.GridSegment
