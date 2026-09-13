/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Theorem55StripCompilerComputability
import LeanTrominoes.PeriodicStripFlatEncoding

/-! # An explicit unary-coordinate encoding for the strip target

The strip height and signed coordinates are unary. This makes the geometric
bounding box polynomial in input length, as required by the strip assertion.
-/

namespace LeanTrominoes.Theorem55StripEncoding
open _root_.Computability

def fields (input : Theorem55.StripInput) : List Nat :=
  [input.1,input.2.length] ++ input.2.flatMap PeriodicStripFlatEncoding.cellFields

def decodeFields : List Nat → Option Theorem55.StripInput
  | height :: count :: rest => do
      let (cells,suffix) ← PeriodicStripFlatEncoding.decodeCells count rest
      if suffix.isEmpty then some (height,cells) else none
  | _ => none

theorem decodeFields_fields (input : Theorem55.StripInput) : decodeFields (fields input) = some input := by
  rcases input with ⟨height,cells⟩
  have parsed : PeriodicStripFlatEncoding.decodeCells cells.length
      (cells.flatMap PeriodicStripFlatEncoding.cellFields) = some (cells,[]) := by
    simpa using PeriodicStripFlatEncoding.decodeCells_flatMap_cellFields_append cells []
  simp [fields,decodeFields,parsed]

/-- Unary fields are runs of true bits terminated by false. -/
def unaryFields (values : List Nat) : List Bool :=
  values.flatMap fun n => List.replicate n true ++ [false]

def decodeUnaryAux : Nat → List Bool → Option (List Nat)
  | 0, [] => some []
  | _+1, [] => none
  | count, true :: rest => decodeUnaryAux (count+1) rest
  | count, false :: rest => (count :: ·) <$> decodeUnaryAux 0 rest

private theorem decodeUnaryAux_replicate (count n : Nat) (rest : List Bool) :
    decodeUnaryAux count (List.replicate n true ++ rest) = decodeUnaryAux (count+n) rest := by
  induction n generalizing count with
  | zero => simp
  | succ n ih => simpa [List.replicate_succ,decodeUnaryAux,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (count+1)

theorem decodeUnaryAux_unaryFields (values : List Nat) : decodeUnaryAux 0 (unaryFields values) = some values := by
  induction values with
  | nil => rfl
  | cons n rest ih =>
    simp only [unaryFields,List.flatMap_cons,List.append_assoc] at *
    rw [decodeUnaryAux_replicate]
    simp [decodeUnaryAux,ih]

def finEncoding : FinEncoding Theorem55.StripInput where
  Γ := Bool
  ΓFin := inferInstance
  encode input := unaryFields (fields input)
  decode symbols := (decodeUnaryAux 0 symbols).bind decodeFields
  decode_encode input := by rw [decodeUnaryAux_unaryFields]; exact decodeFields_fields input

end LeanTrominoes.Theorem55StripEncoding

namespace LeanTrominoes.Theorem55

/-- The strip assertion with explicit unary height and coordinate fields. -/
def stripStatement : Prop := Complexity.PSPACEComplete Theorem55StripEncoding.finEncoding stripProblem

end LeanTrominoes.Theorem55
