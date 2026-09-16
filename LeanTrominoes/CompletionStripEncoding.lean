/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicTrominoCompletion
import LeanTrominoes.PeriodicStripFlatEncoding

/-! # Unary geometric encoding for strip completion

Height, period, motif length, symmetries, and signed coordinates are explicit
unary fields. In particular the rectangular fundamental domain has area at
most the square of the input length. No promises exclude invalid prefills.
-/
namespace LeanTrominoes.CompletionStripEncoding
open _root_.Computability

def symmetryCode : SquareSymmetry → Nat
  | .identity => 0
  | .rotate90 => 1
  | .rotate180 => 2
  | .rotate270 => 3
  | .reflectX => 4
  | .reflectDiagonal => 5
  | .reflectY => 6
  | .reflectAntidiagonal => 7

def decodeSymmetry : Nat → Option SquareSymmetry
  | 0 => some .identity
  | 1 => some .rotate90
  | 2 => some .rotate180
  | 3 => some .rotate270
  | 4 => some .reflectX
  | 5 => some .reflectDiagonal
  | 6 => some .reflectY
  | 7 => some .reflectAntidiagonal
  | _ => none

@[simp] theorem decodeSymmetry_code (s : SquareSymmetry) :
    decodeSymmetry (symmetryCode s) = some s := by cases s <;> rfl

def placementFields (p : Placement Unit) : List Nat :=
  [symmetryCode p.symmetry,Encodable.encode p.offset.1,Encodable.encode p.offset.2]

def decodePlacement : List Nat → Option (Placement Unit × List Nat)
  | s :: x :: y :: rest => do
      let symmetry ← decodeSymmetry s
      pure (⟨(),symmetry,PeriodicCNFFlatEncoding.decodeIntField x,
        PeriodicCNFFlatEncoding.decodeIntField y⟩,rest)
  | _ => none

theorem decodePlacement_fields (p : Placement Unit) (rest : List Nat) :
    decodePlacement (placementFields p ++ rest) = some (p,rest) := by
  cases p with
  | mk kind symmetry offset =>
    cases kind
    cases offset
    simp [placementFields,decodePlacement]

def decodePlacements : Nat → List Nat → Option (List (Placement Unit) × List Nat)
  | 0,fields => some ([],fields)
  | n+1,fields => do
      let (p,rest) ← decodePlacement fields
      let (ps,suffix) ← decodePlacements n rest
      pure (p::ps,suffix)

theorem decodePlacements_fields (ps : List (Placement Unit)) (rest : List Nat) :
    decodePlacements ps.length (ps.flatMap placementFields ++ rest) = some (ps,rest) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [decodePlacements,List.append_assoc,decodePlacement_fields,ih]

def fields (input : PeriodicStripTrominoPrefill) : List Nat :=
  [input.height,input.period,input.motif.length] ++ input.motif.flatMap placementFields

def decodeFields : List Nat → Option PeriodicStripTrominoPrefill
  | height :: period :: count :: rest => do
      let (motif,suffix) ← decodePlacements count rest
      if suffix.isEmpty then some ⟨motif,height,period⟩ else none
  | _ => none

theorem decodeFields_fields (input : PeriodicStripTrominoPrefill) :
    decodeFields (fields input) = some input := by
  have parsed := decodePlacements_fields input.motif []
  simp only [List.append_nil] at parsed
  cases input
  simp_all [fields,decodeFields]

def unaryFields (values : List Nat) : List Bool :=
  values.flatMap fun n => List.replicate n true ++ [false]

def decodeUnaryAux : Nat → List Bool → Option (List Nat)
  | 0,[] => some []
  | _+1,[] => none
  | n,true::rest => decodeUnaryAux (n+1) rest
  | n,false::rest => (n::·) <$> decodeUnaryAux 0 rest

private theorem decodeUnaryAux_replicate (count n : Nat) (rest : List Bool) :
    decodeUnaryAux count (List.replicate n true ++ rest) = decodeUnaryAux (count+n) rest := by
  induction n generalizing count with
  | zero => simp
  | succ n ih => simpa [List.replicate_succ,decodeUnaryAux,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (count+1)

theorem decodeUnaryAux_unaryFields (values : List Nat) :
    decodeUnaryAux 0 (unaryFields values) = some values := by
  induction values with
  | nil => rfl
  | cons n rest ih =>
    simp only [unaryFields,List.flatMap_cons,List.append_assoc] at *
    rw [decodeUnaryAux_replicate]
    simp [decodeUnaryAux,ih]

def finEncoding : FinEncoding PeriodicStripTrominoPrefill where
  Γ := Bool
  ΓFin := inferInstance
  encode input := unaryFields (fields input)
  decode symbols := (decodeUnaryAux 0 symbols).bind decodeFields
  decode_encode input := by rw [decodeUnaryAux_unaryFields]; exact decodeFields_fields input

theorem unaryFields_length (values : List Nat) :
    (unaryFields values).length = values.sum + values.length := by
  induction values with
  | nil => rfl
  | cons n rest ih => simp [unaryFields] at ih ⊢; omega

theorem height_le_length (input : PeriodicStripTrominoPrefill) :
    input.height ≤ (finEncoding.encode input).length := by
  simp [finEncoding,unaryFields_length,fields]
  omega

theorem period_le_length (input : PeriodicStripTrominoPrefill) :
    input.period ≤ (finEncoding.encode input).length := by
  simp [finEncoding,unaryFields_length,fields]
  omega

theorem area_le_length_sq (input : PeriodicStripTrominoPrefill) :
    input.period * input.height ≤ (finEncoding.encode input).length ^ 2 := by
  simpa [pow_two] using Nat.mul_le_mul (period_le_length input) (height_le_length input)

end LeanTrominoes.CompletionStripEncoding
