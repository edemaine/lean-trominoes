/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFUnaryProgramClauseProfileData

/-! # Finite final ordering of Figure 9 output clauses -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeFigureNineFinalClauseOrdering

open UnaryProgramClauseProfile

universe u

/-- Stable clockwise ordering induced by the unit-elimination clause exits.
Binary clauses leave west/east and ternary clauses leave south/west/east, so
their final orders are respectively `1,0` and `2,0,1`. -/
def reorderList {Value : Type u} : List Value → List Value
  | [first, second] => [second, first]
  | [first, second, third] => [third, first, second]
  | values => values

/-- The same final permutation on a finite nonempty width-three profile. -/
def reorderProfile : ClauseProfile → ClauseProfile
  | .unary first => .unary first
  | .binary first second => .binary second first
  | .ternary first second third => .ternary third first second

@[simp] theorem reorderProfile_literals (profile : ClauseProfile) :
    (reorderProfile profile).literals = reorderList profile.literals := by
  cases profile <;> rfl

@[simp] theorem reorderList_length {Value : Type u} (values : List Value) :
    (reorderList values).length = values.length := by
  rcases values with _ | ⟨first, rest⟩
  · rfl
  · rcases rest with _ | ⟨second, rest⟩
    · rfl
    · rcases rest with _ | ⟨third, rest⟩
      · rfl
      · rcases rest with _ | ⟨fourth, rest⟩ <;> rfl

@[simp] theorem reorderProfile_length (profile : ClauseProfile) :
    (reorderProfile profile).literals.length = profile.literals.length := by
  rw [reorderProfile_literals, reorderList_length]

/-- Reordering a block never introduces a value not already in that block. -/
theorem mem_of_mem_reorderList {Value : Type u} {value : Value}
    {values : List Value} (member : value ∈ reorderList values) :
    value ∈ values := by
  have permutation : (reorderList values).Perm values := by
    rcases values with _ | ⟨first, rest⟩
    · simp [reorderList]
    · rcases rest with _ | ⟨second, rest⟩
      · simp [reorderList]
      · rcases rest with _ | ⟨third, rest⟩
        · exact List.Perm.swap first second []
        · rcases rest with _ | ⟨fourth, rest⟩
          · exact
              (List.Perm.swap first third [second]).trans
                ((List.Perm.swap second third []).cons first)
          · simp [reorderList]
  exact permutation.mem_iff.mp member

end FormulaShapeFigureNineFinalClauseOrdering
end PeriodicCNF
end LeanTrominoes
