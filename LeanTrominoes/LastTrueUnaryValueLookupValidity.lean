/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastTrueUnaryValueLookupInput

/-! # Constructing last-true lookup alignment promises -/

namespace LeanTrominoes
namespace LastTrueUnaryValueLookupMachine

def RowValid.of_length_eq {row : List Bool} {values : List Nat}
    (lengthEq : row.length = values.length) : RowValid row values := by
  induction row generalizing values with
  | nil =>
      cases values with
      | nil => exact .nil
      | cons value values => simp at lengthEq
  | cons bit bits induction =>
      cases values with
      | nil => simp at lengthEq
      | cons value values =>
          exact .cons (induction (by simpa using lengthEq))

def RowsValid.of_forall_length {rows : List (List Bool)}
    {values : List Nat}
    (lengths : rows.Forall fun row => row.length = values.length) :
    RowsValid values rows := by
  induction rows with
  | nil => exact .nil
  | cons row rows induction =>
      rw [List.forall_cons] at lengths
      exact .cons
        (RowValid.of_length_eq lengths.1)
        (induction lengths.2)

end LastTrueUnaryValueLookupMachine
end LeanTrominoes
