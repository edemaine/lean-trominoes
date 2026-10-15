/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.FiniteRationalPerturbation

/-! # Finite affine perturbation reflects the lexicographic order -/
namespace LeanTrominoes.RationalPerturbation

theorem evaluate_lt_iff {values : List (ℚ × ℚ)} {epsilon : ℚ} (positive : 0 < epsilon)
    (small : epsilon ≤ margin values) {first second : ℚ × ℚ}
    (firstMember : first ∈ values) (secondMember : second ∈ values) :
    evaluate epsilon first < evaluate epsilon second ↔ Before first second := by
  constructor
  · intro ordered
    rcases lt_trichotomy first.1 second.1 with less | equal | greater
    · exact Or.inl less
    · right
      refine ⟨equal,?_⟩
      unfold evaluate at ordered
      rw [equal] at ordered
      nlinarith
    · exact (not_lt_of_gt (evaluate_order positive small secondMember firstMember (Or.inl greater)) ordered).elim
  · exact evaluate_order positive small firstMember secondMember

theorem evaluate_injective_on {values : List (ℚ × ℚ)} {epsilon : ℚ} (positive : 0 < epsilon)
    (small : epsilon ≤ margin values) {first second : ℚ × ℚ}
    (firstMember : first ∈ values) (secondMember : second ∈ values)
    (equal : evaluate epsilon first = evaluate epsilon second) : first = second := by
  have baseEqual : first.1 = second.1 := by
    rcases lt_trichotomy first.1 second.1 with less | same | greater
    · have ordered := evaluate_order positive small firstMember secondMember (Or.inl less)
      linarith
    · exact same
    · have ordered := evaluate_order positive small secondMember firstMember (Or.inl greater)
      linarith
  apply Prod.ext baseEqual
  unfold evaluate at equal
  rw [baseEqual] at equal
  nlinarith

end LeanTrominoes.RationalPerturbation
