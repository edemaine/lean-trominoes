/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.LastTrueUnaryValueLookupMachine

/-! # Promised inputs for last-true unary lookup -/

namespace LeanTrominoes
namespace LastTrueUnaryValueLookupMachine

/-- Informative evidence that one Boolean row and the value list have equal
length. -/
inductive RowValid : List Bool → List Nat → Type
  | nil : RowValid [] []
  | cons {bit : Bool} {value : Nat} {bits : List Bool} {values : List Nat}
      (rest : RowValid bits values) :
      RowValid (bit :: bits) (value :: values)

/-- Every row is aligned with the same reusable value list. -/
inductive RowsValid (values : List Nat) : List (List Bool) → Type
  | nil : RowsValid values []
  | cons {row : List Bool} {rows : List (List Bool)}
      (rowValid : RowValid row values) (rest : RowsValid values rows) :
      RowsValid values (row :: rows)

structure Input where
  rows : List (List Bool)
  values : List Nat
  valid : RowsValid values rows

def encode (input : Input) : List InputSymbol :=
  SeparatedProductEncoding.encode
    (fun rows => DelimitedBinaryWords.encode ⟨rows⟩)
    UnaryFieldEncoderMachine.unaryFields
    (input.rows, input.values)

def outputEncoding (input : Input) : List UnarySymbol :=
  UnaryFieldEncoderMachine.unaryFields
    (lookups input.rows input.values)

theorem RowValid.length_eq {row : List Bool} {values : List Nat}
    (valid : RowValid row values) : row.length = values.length := by
  induction valid with
  | nil => rfl
  | cons _ induction => simp [induction]

theorem RowsValid.forall_length {rows : List (List Bool)}
    {values : List Nat} (valid : RowsValid values rows) :
    rows.Forall fun row => row.length = values.length := by
  induction valid with
  | nil => simp
  | cons rowValid rest induction =>
      simp [rowValid.length_eq, induction]

end LastTrueUnaryValueLookupMachine
end LeanTrominoes
