/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GridSegmentCollinearIntervals
import LeanTrominoes.GridSegmentNonparallelSeparation
import LeanTrominoes.GridSegmentRealLineCharacterization

/-! # Integer separators for parallel segments, including point segments -/
namespace LeanTrominoes.GridSegment

private theorem interval_gap_of_four_exclusions (a b c d : Int)
    (_firstStart : ¬(min c d≤a ∧ a≤max c d)) (firstFinish : ¬(min c d≤b ∧ b≤max c d))
    (secondStart : ¬(min a b≤c ∧ c≤max a b)) (secondFinish : ¬(min a b≤d ∧ d≤max a b)) :
    max a b<min c d ∨ max c d<min a b := by omega

theorem collinear_x_interval_gap {first second : GridSegment}
    (firstNonzero : first.direction.1≠0) (secondNonzero : second.direction.1≠0)
    (firstStart : first.side second.start=0) (firstFinish : first.side second.finish=0)
    (secondStart : second.side first.start=0) (secondFinish : second.side first.finish=0)
    (disjoint : ∀ p : ℝ × ℝ, first.RealContains p → ¬second.RealContains p) :
    max first.start.1 first.finish.1<min second.start.1 second.finish.1 ∨
      max second.start.1 second.finish.1<min first.start.1 first.finish.1 := by
  apply interval_gap_of_four_exclusions
  · intro bounds
    exact disjoint _ (realContains_start first) (realContains_of_collinear_x secondNonzero secondStart bounds)
  · intro bounds
    exact disjoint _ (realContains_finish first) (realContains_of_collinear_x secondNonzero secondFinish bounds)
  · intro bounds
    exact disjoint _ (realContains_of_collinear_x firstNonzero firstStart bounds) (realContains_start second)
  · intro bounds
    exact disjoint _ (realContains_of_collinear_x firstNonzero firstFinish bounds) (realContains_finish second)

private theorem separator_of_x_gap {bound : Int} (positive : 1≤bound) {first second : GridSegment}
    (gap : max first.start.1 first.finish.1<min second.start.1 second.finish.1 ∨
      max second.start.1 second.finish.1<min first.start.1 first.finish.1) :
    ∃ n : Cell, (|n.1|≤bound ∧ |n.2|≤bound) ∧ StrictlySeparated n first second := by
  rcases gap with forward | backward
  · exact ⟨(1,0),by norm_num; omega,strictlySeparated_x forward⟩
  · exact ⟨(-1,0),by norm_num; omega,by simpa using (strictlySeparated_x backward).negate_swap⟩

theorem parallel_x_integer_separator {bound : Int} (positive : 1≤bound) {first second : GridSegment}
    (firstBounds : |first.direction.1|≤bound ∧ |first.direction.2|≤bound)
    (firstNonzero : first.direction.1≠0) (parallel : cross first.direction second.direction=0)
    (disjoint : ∀ p : ℝ × ℝ, first.RealContains p → ¬second.RealContains p) :
    ∃ n : Cell, (|n.1|≤bound ∧ |n.2|≤bound) ∧ StrictlySeparated n first second := by
  have difference := sides_difference first second
  rw [parallel] at difference
  have same : first.side second.start=first.side second.finish := by omega
  have normalBounds : |first.normal.1|≤bound ∧ |first.normal.2|≤bound := by
    simpa only [normal,abs_neg] using And.intro firstBounds.2 firstBounds.1
  by_cases above : 0<first.side second.start
  · exact ⟨first.normal,normalBounds,strictlySeparated_of_positive_sides above (by omega)⟩
  · by_cases below : first.side second.start<0
    · exact ⟨(-first.normal.1,-first.normal.2),by simpa only [abs_neg] using normalBounds,
        strictlySeparated_of_negative_sides below (by omega)⟩
    · have collinearStart : first.side second.start=0 := by omega
      have collinearFinish : first.side second.finish=0 := by omega
      by_cases secondNonzero : second.direction.1≠0
      · have reverseStart : second.side first.start=0 := by
          have identity : first.direction.1*second.side first.start=
              -second.direction.1*first.side second.start +
                (second.start.1-first.start.1)*cross first.direction second.direction := by
            simp only [side,cross,direction]
            ring
          simp only [collinearStart,parallel,mul_zero,add_zero] at identity
          exact (mul_eq_zero.mp identity).resolve_left firstNonzero
        have reverseDifference := sides_difference second first
        rw [cross_swap second.direction first.direction,parallel,neg_zero] at reverseDifference
        have reverseFinish : second.side first.finish=0 := by omega
        exact separator_of_x_gap positive (collinear_x_interval_gap firstNonzero secondNonzero
          collinearStart collinearFinish reverseStart reverseFinish disjoint)
      · have secondX : second.direction.1=0 := by omega
        have equalX : second.start.1=second.finish.1 := (sub_eq_zero.mp secondX).symm
        have outside : ¬(min first.start.1 first.finish.1≤second.start.1 ∧
            second.start.1≤max first.start.1 first.finish.1) := by
          intro inside
          exact disjoint _ (realContains_of_collinear_x firstNonzero collinearStart inside) (realContains_start second)
        apply separator_of_x_gap positive
        simp only [← equalX,min_self,max_self]
        omega

theorem vertical_contains_iff {s : GridSegment} {p : Cell}
    (vertical : s.start.1=s.finish.1) (sameX : p.1=s.start.1) :
    s.RealContains ((p.1:ℝ),(p.2:ℝ)) ↔ min s.start.2 s.finish.2≤p.2 ∧ p.2≤max s.start.2 s.finish.2 := by
  rw [realContains_iff_box_and_line]
  simp only [RealBoxContains,RealLineContains,← vertical,sameX,min_self,max_self,
    sub_self,zero_mul,mul_zero,le_refl,true_and,and_true]
  exact_mod_cast Iff.rfl

theorem vertical_integer_separator {bound : Int} (positive : 1≤bound) {first second : GridSegment}
    (firstVertical : first.start.1=first.finish.1) (secondVertical : second.start.1=second.finish.1)
    (disjoint : ∀ p : ℝ × ℝ, first.RealContains p → ¬second.RealContains p) :
    ∃ n : Cell, (|n.1|≤bound ∧ |n.2|≤bound) ∧ StrictlySeparated n first second := by
  by_cases sameX : first.start.1=second.start.1
  · have gap : max first.start.2 first.finish.2<min second.start.2 second.finish.2 ∨
        max second.start.2 second.finish.2<min first.start.2 first.finish.2 := by
      apply interval_gap_of_four_exclusions
      · intro inside
        exact disjoint _ (realContains_start first) ((vertical_contains_iff secondVertical sameX).mpr inside)
      · intro inside
        exact disjoint _ (realContains_finish first)
          ((vertical_contains_iff secondVertical (firstVertical.symm.trans sameX)).mpr inside)
      · intro inside
        exact disjoint _ ((vertical_contains_iff firstVertical sameX.symm).mpr inside) (realContains_start second)
      · intro inside
        exact disjoint _ ((vertical_contains_iff firstVertical (secondVertical.symm.trans sameX.symm)).mpr inside)
          (realContains_finish second)
    rcases gap with forward | backward
    · exact ⟨(0,1),by norm_num; omega,strictlySeparated_y forward⟩
    · exact ⟨(0,-1),by norm_num; omega,by simpa using (strictlySeparated_y backward).negate_swap⟩
  · apply separator_of_x_gap positive
    simp only [← firstVertical,← secondVertical,min_self,max_self]
    omega

theorem integer_separator {bound : Int} (positive : 1≤bound) {first second : GridSegment}
    (firstBounds : |first.direction.1|≤bound ∧ |first.direction.2|≤bound)
    (secondBounds : |second.direction.1|≤bound ∧ |second.direction.2|≤bound)
    (disjoint : ∀ p : ℝ × ℝ, first.RealContains p → ¬second.RealContains p) :
    ∃ n : Cell, (|n.1|≤bound ∧ |n.2|≤bound) ∧ StrictlySeparated n first second := by
  by_cases nonparallel : cross first.direction second.direction≠0
  · exact nonparallel_integer_separator firstBounds secondBounds nonparallel disjoint
  · have parallel : cross first.direction second.direction=0 := by omega
    by_cases firstNonzero : first.direction.1≠0
    · exact parallel_x_integer_separator positive firstBounds firstNonzero parallel disjoint
    · by_cases secondNonzero : second.direction.1≠0
      · have reverse : cross second.direction first.direction=0 := by rw [cross_swap,parallel,neg_zero]
        obtain ⟨n,bounds,separated⟩ := parallel_x_integer_separator positive secondBounds secondNonzero reverse
          (fun p secondMember firstMember => disjoint p firstMember secondMember)
        exact ⟨(-n.1,-n.2),by simpa only [abs_neg] using bounds,separated.negate_swap⟩
      · have firstVertical : first.start.1=first.finish.1 := by simp only [direction] at firstNonzero; omega
        have secondVertical : second.start.1=second.finish.1 := by simp only [direction] at secondNonzero; omega
        exact vertical_integer_separator positive firstVertical secondVertical disjoint

theorem perturbations_disjoint {bound factor : Int} (positive : 1≤bound) (spacing : 4*bound<factor)
    {first second firstOutput secondOutput : GridSegment}
    (firstBounds : |first.direction.1|≤bound ∧ |first.direction.2|≤bound)
    (secondBounds : |second.direction.1|≤bound ∧ |second.direction.2|≤bound)
    (disjoint : ∀ p : ℝ × ℝ, first.RealContains p → ¬second.RealContains p)
    (firstPerturbed : EndpointPerturbation factor first firstOutput)
    (secondPerturbed : EndpointPerturbation factor second secondOutput) :
    ∀ p : ℝ × ℝ, firstOutput.RealContains p → ¬secondOutput.RealContains p := by
  obtain ⟨n,bounds,separated⟩ := integer_separator positive firstBounds secondBounds disjoint
  exact (separated.perturb (by omega) spacing bounds firstPerturbed secondPerturbed).no_common_point

end LeanTrominoes.GridSegment
