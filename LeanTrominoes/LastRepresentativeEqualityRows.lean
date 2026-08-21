/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWords

/-! # Last-representative rows of a Boolean equality matrix -/

namespace LeanTrominoes
namespace LastRepresentativeEqualityRows

/-- A row represents its equality class in Lean's `List.dedup` order exactly
when no strictly later column is equal to it. -/
def selected (rowIndex : Nat) (row : List Bool) : Bool :=
  !(row.drop (rowIndex + 1)).contains true

def rowsAux : Nat → List (List Bool) → List (List Bool)
  | _, [] => []
  | rowIndex, row :: rows =>
      if selected rowIndex row then
        row :: rowsAux (rowIndex + 1) rows
      else
        rowsAux (rowIndex + 1) rows

/-- Equality rows at the last presentation occurrence of each class, retained
in increasing presentation order. -/
def rows (input : DelimitedBinaryWords.Input) :
    DelimitedBinaryWords.Input :=
  ⟨rowsAux 0 input.words⟩

@[simp] theorem rowsAux_nil (rowIndex : Nat) :
    rowsAux rowIndex [] = [] := rfl

@[simp] theorem rowsAux_cons_selected (rowIndex : Nat) (row : List Bool)
    (rows : List (List Bool)) (isSelected : selected rowIndex row = true) :
    rowsAux rowIndex (row :: rows) =
      row :: rowsAux (rowIndex + 1) rows := by
  simp [rowsAux, isSelected]

@[simp] theorem rowsAux_cons_rejected (rowIndex : Nat) (row : List Bool)
    (rows : List (List Bool)) (isRejected : selected rowIndex row = false) :
    rowsAux rowIndex (row :: rows) = rowsAux (rowIndex + 1) rows := by
  simp [rowsAux, isRejected]

theorem selected_eq_true_iff (rowIndex : Nat) (row : List Bool) :
    selected rowIndex row = true ↔
      true ∉ row.drop (rowIndex + 1) := by
  simp [selected]

end LastRepresentativeEqualityRows
end LeanTrominoes
