/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListRangeGetDIndex
import LeanTrominoes.PeriodicCNFFormulaShapeFigureNineFinalClauseOrderingData

/-! # Total lookups through the final Figure 9 clause permutation -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeFigureNineFinalClauseOrdering

universe u

/-- A range of length at least four is outside the two exceptional Figure 9
clause arities, so `reorderList` leaves it unchanged. -/
theorem reorderList_range_eq_self_of_four_le
    (size : Nat) (fourLe : 4 ≤ size) :
    reorderList (List.range size) = List.range size := by
  generalize rangeEq : List.range size = values
  have lengthEq : values.length = size := by
    rw [← rangeEq]
    simp
  rcases values with _ | ⟨first, rest⟩
  · simp at lengthEq
    omega
  rcases rest with _ | ⟨second, rest⟩
  · simp at lengthEq
    omega
  rcases rest with _ | ⟨third, rest⟩
  · simp at lengthEq
    omega
  rcases rest with _ | ⟨fourth, rest⟩
  · simp at lengthEq
    omega
  rfl

/-- At every genuine final position, lookup after `reorderList` is lookup in
the original list at the correspondingly reordered source index. -/
theorem reorderList_getD_eq_sourceIndex
    {Value : Type u} (values : List Value) (default : Value)
    (index : Nat) (indexLt : index < values.length) :
    (reorderList values).getD index default =
      values.getD
        ((reorderList (List.range values.length)).getD index 0)
        default := by
  rcases values with _ | ⟨first, rest⟩
  · simp at indexLt
  rcases rest with _ | ⟨second, rest⟩
  · simp only [List.length_cons, List.length_nil] at indexLt
    have indexEq : index = 0 := by omega
    subst index
    rfl
  rcases rest with _ | ⟨third, rest⟩
  · simp only [List.length_cons, List.length_nil] at indexLt
    have indexEq : index = 0 ∨ index = 1 := by omega
    rcases indexEq with rfl | rfl <;> rfl
  rcases rest with _ | ⟨fourth, rest⟩
  · simp only [List.length_cons, List.length_nil] at indexLt
    have indexEq : index = 0 ∨ index = 1 ∨ index = 2 := by omega
    rcases indexEq with rfl | rfl | rfl <;> rfl
  have fourLe : 4 ≤
      (first :: second :: third :: fourth :: rest).length := by
    simp
  rw [show
      reorderList (first :: second :: third :: fourth :: rest) =
        first :: second :: third :: fourth :: rest by rfl,
    reorderList_range_eq_self_of_four_le _ fourLe]
  exact
    (List.getD_range_getD
      (first :: second :: third :: fourth :: rest)
      default _ index indexLt).symm

end FormulaShapeFigureNineFinalClauseOrdering
end PeriodicCNF
end LeanTrominoes
