/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

/-! # Computable rational perturbations realizing a finite lexicographic order

A single positive rational perturbation preserves every strict comparison
of affine coordinates in a finite family, breaking equal-coordinate ties
by their slopes.
-/
namespace LeanTrominoes.RationalPerturbation

def positiveMargin (values : List ℚ) : ℚ := values.foldr min 1

theorem positiveMargin_positive {values : List ℚ} (positive : ∀ value ∈ values, 0 < value) :
    0 < positiveMargin values := by
  induction values with
  | nil => norm_num [positiveMargin]
  | cons head tail induction =>
    exact lt_min (positive head (by simp)) (induction (fun value member => positive value (by simp [member])))

theorem positiveMargin_le {values : List ℚ} {value : ℚ} (member : value ∈ values) :
    positiveMargin values ≤ value := by
  induction values with
  | nil => simp at member
  | cons head tail induction =>
    rcases List.mem_cons.mp member with rfl | member
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (induction member)

def pairBound (first second : ℚ × ℚ) : ℚ :=
  if first.1 < second.1 then (second.1-first.1)/(1+|second.2-first.2|) else 1

def margin (values : List (ℚ × ℚ)) : ℚ :=
  positiveMargin (values.flatMap fun first => values.map (pairBound first))

def evaluate (epsilon : ℚ) (coordinate : ℚ × ℚ) : ℚ := coordinate.1+epsilon*coordinate.2

def Before (first second : ℚ × ℚ) : Prop :=
  first.1 < second.1 ∨ (first.1 = second.1 ∧ first.2 < second.2)

theorem pairBound_positive (first second : ℚ × ℚ) : 0 < pairBound first second := by
  unfold pairBound
  split_ifs with ordered
  · exact div_pos (sub_pos.mpr ordered) (by positivity)
  · norm_num

theorem margin_positive (values : List (ℚ × ℚ)) : 0 < margin values := by
  apply positiveMargin_positive
  intro bound member
  obtain ⟨first,_,mappedMember⟩ := List.mem_flatMap.mp member
  obtain ⟨second,_,rfl⟩ := List.mem_map.mp mappedMember
  exact pairBound_positive first second

theorem margin_le_pairBound {values : List (ℚ × ℚ)} {first second : ℚ × ℚ}
    (firstMember : first ∈ values) (secondMember : second ∈ values) : margin values ≤ pairBound first second :=
  positiveMargin_le (List.mem_flatMap.mpr ⟨first,firstMember,List.mem_map.mpr ⟨second,secondMember,rfl⟩⟩)

theorem evaluate_order {values : List (ℚ × ℚ)} {epsilon : ℚ} (positive : 0 < epsilon)
    (small : epsilon ≤ margin values) {first second : ℚ × ℚ}
    (firstMember : first ∈ values) (secondMember : second ∈ values) (ordered : Before first second) :
    evaluate epsilon first < evaluate epsilon second := by
  rcases ordered with separated | ⟨same,slopes⟩
  · have bound := small.trans (margin_le_pairBound firstMember secondMember)
    simp only [pairBound,if_pos separated] at bound
    have scaled := (le_div_iff₀ (by positivity : (0 : ℚ) < 1+|second.2-first.2|)).mp bound
    have slopeBound := neg_abs_le (second.2-first.2)
    have scaledSlope := mul_le_mul_of_nonneg_left slopeBound positive.le
    unfold evaluate
    nlinarith
  · unfold evaluate
    rw [same]
    nlinarith

end LeanTrominoes.RationalPerturbation
