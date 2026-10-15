/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Common.Geometry.GridSegmentRationalXParameter

/-! # Parameter order and closed intervals for either direction of a straight edge -/
namespace LeanTrominoes.GridSegment

theorem rationalXParameter_le_iff {segment : GridSegment}
    (forward : segment.start.1 < segment.finish.1) (first last : ℚ) :
    segment.rationalXParameter first ≤ segment.rationalXParameter last ↔ first ≤ last := by
  have positive : (0 : ℚ) < (segment.finish.1 : ℚ)-segment.start.1 := by exact_mod_cast sub_pos.mpr forward
  unfold rationalXParameter
  rw [div_le_iff₀ positive,div_mul_cancel₀ _ positive.ne']
  constructor <;> intro bound <;> linarith

theorem rationalXParameter_le_iff_of_reverse {segment : GridSegment}
    (backward : segment.finish.1 < segment.start.1) (first last : ℚ) :
    segment.rationalXParameter first ≤ segment.rationalXParameter last ↔ last ≤ first := by
  have negative : (segment.finish.1 : ℚ)-(segment.start.1 : ℚ) < 0 := by exact_mod_cast sub_neg.mpr backward
  unfold rationalXParameter
  rw [div_le_iff_of_neg negative,div_mul_cancel₀ _ negative.ne]
  constructor <;> intro bound <;> linarith

theorem rationalXParameter_between_iff {segment : GridSegment}
    (nonvertical : segment.start.1 ≠ segment.finish.1) (first last coordinate : ℚ) :
    (min (segment.rationalXParameter first) (segment.rationalXParameter last) ≤ segment.rationalXParameter coordinate ∧
      segment.rationalXParameter coordinate ≤ max (segment.rationalXParameter first) (segment.rationalXParameter last)) ↔
      min first last ≤ coordinate ∧ coordinate ≤ max first last := by
  rcases lt_or_gt_of_ne nonvertical with forward | backward
  · rcases le_total first last with before | after
    · have mapped := (rationalXParameter_le_iff forward first last).mpr before
      simp only [min_eq_left before,max_eq_right before,min_eq_left mapped,max_eq_right mapped,
        rationalXParameter_le_iff forward]
    · have mapped := (rationalXParameter_le_iff forward last first).mpr after
      simp only [min_eq_right after,max_eq_left after,min_eq_right mapped,max_eq_left mapped,
        rationalXParameter_le_iff forward]
  · rcases le_total first last with before | after
    · have mapped := (rationalXParameter_le_iff_of_reverse backward last first).mpr before
      simp only [min_eq_left before,max_eq_right before,min_eq_right mapped,max_eq_left mapped,
        rationalXParameter_le_iff_of_reverse backward]
      exact and_comm
    · have mapped := (rationalXParameter_le_iff_of_reverse backward first last).mpr after
      simp only [min_eq_right after,max_eq_left after,min_eq_left mapped,max_eq_right mapped,
        rationalXParameter_le_iff_of_reverse backward]
      exact and_comm

theorem rationalXParameter_lt_iff {segment : GridSegment}
    (forward : segment.start.1 < segment.finish.1) (first last : ℚ) :
    segment.rationalXParameter first < segment.rationalXParameter last ↔ first < last := by
  simp only [lt_iff_not_ge,rationalXParameter_le_iff forward]

theorem rationalXParameter_lt_iff_of_reverse {segment : GridSegment}
    (backward : segment.finish.1 < segment.start.1) (first last : ℚ) :
    segment.rationalXParameter first < segment.rationalXParameter last ↔ last < first := by
  simp only [lt_iff_not_ge,rationalXParameter_le_iff_of_reverse backward]

theorem rationalXParameter_between_open_iff {segment : GridSegment}
    (nonvertical : segment.start.1 ≠ segment.finish.1) (first last coordinate : ℚ) :
    (min (segment.rationalXParameter first) (segment.rationalXParameter last) < segment.rationalXParameter coordinate ∧
      segment.rationalXParameter coordinate < max (segment.rationalXParameter first) (segment.rationalXParameter last)) ↔
      min first last < coordinate ∧ coordinate < max first last := by
  rcases lt_or_gt_of_ne nonvertical with forward | backward
  · simp only [min_lt_iff,lt_max_iff,rationalXParameter_lt_iff forward]
  · simp only [min_lt_iff,lt_max_iff,rationalXParameter_lt_iff_of_reverse backward]
    exact and_comm

def rationalXAtParameter (segment : GridSegment) (parameter : ℚ) : ℚ :=
  segment.start.1+parameter*((segment.finish.1 : ℚ)-segment.start.1)

theorem rationalXParameter_xAtParameter {segment : GridSegment}
    (nonvertical : segment.start.1 ≠ segment.finish.1) (parameter : ℚ) :
    segment.rationalXParameter (segment.rationalXAtParameter parameter) = parameter := by
  have nonzero : (segment.finish.1 : ℚ)-(segment.start.1 : ℚ) ≠ 0 := by
    intro zero
    apply nonvertical
    exact_mod_cast (by linarith : (segment.start.1 : ℚ) = segment.finish.1)
  simp only [rationalXParameter,rationalXAtParameter,add_sub_cancel_left,mul_div_cancel_right₀ _ nonzero]

theorem rationalXAtParameter_parameter (segment : GridSegment) (coordinate : ℚ)
    (nonvertical : segment.start.1 ≠ segment.finish.1) :
    segment.rationalXAtParameter (segment.rationalXParameter coordinate) = coordinate := by
  have nonzero : (segment.finish.1 : ℚ)-(segment.start.1 : ℚ) ≠ 0 := by
    intro zero
    apply nonvertical
    exact_mod_cast (by linarith : (segment.start.1 : ℚ) = segment.finish.1)
  simp only [rationalXParameter,rationalXAtParameter,div_mul_cancel₀ _ nonzero]
  ring

def rationalPointAtParameter (segment : GridSegment) (parameter : ℚ) : ℚ × ℚ :=
  (segment.rationalXAtParameter parameter,
    segment.start.2+parameter*((segment.finish.2 : ℚ)-segment.start.2))

theorem rationalPointAtParameter_translate (segment : GridSegment) (offset : Cell) (parameter : ℚ) :
    (segment.translate offset).rationalPointAtParameter parameter =
      ((segment.rationalPointAtParameter parameter).1+(offset.1 : ℚ),
        (segment.rationalPointAtParameter parameter).2+(offset.2 : ℚ)) := by
  apply Prod.ext <;> simp [rationalPointAtParameter,rationalXAtParameter,translate,Cell.add] <;> ring

theorem rationalPointAtParameter_realContains (segment : GridSegment) {parameter : ℚ}
    (lower : 0 ≤ parameter) (upper : parameter ≤ 1) :
    segment.RealContains (((segment.rationalPointAtParameter parameter).1 : ℝ),
      ((segment.rationalPointAtParameter parameter).2 : ℝ)) := by
  refine ⟨(parameter : ℝ),by exact_mod_cast lower,by exact_mod_cast upper,?_,?_⟩
  all_goals simp only [rationalPointAtParameter,rationalXAtParameter]; push_cast; ring

theorem rationalPointAtParameter_height {segment : GridSegment}
    (nonvertical : segment.start.1 ≠ segment.finish.1) (parameter : ℚ) :
    segment.rationalHeightAt (segment.rationalPointAtParameter parameter).1 =
      (segment.rationalPointAtParameter parameter).2 := by
  have nonzero : (segment.finish.1 : ℚ)-(segment.start.1 : ℚ) ≠ 0 := by
    intro zero
    apply nonvertical
    exact_mod_cast (by linarith : (segment.start.1 : ℚ) = segment.finish.1)
  simp only [rationalHeightAt,rationalAbscissaAt,swapAxes,rationalPointAtParameter,rationalXAtParameter]
  dsimp only [Prod.fst,Prod.snd,Prod.swap]
  field_simp
  ring

end LeanTrominoes.GridSegment
