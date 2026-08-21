/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Data.List.SplitLengths
import LeanTrominoes.BoolSquareRowsSequenceExecution

/-! # Square Boolean matrices encoded in row-major order -/

noncomputable section

namespace LeanTrominoes
namespace BoolSquareRows

open Computability
open BoolSquareRowsMachine

/-- A flat Boolean word together with the promise needed by the row reshaper. -/
structure Input where
  bits : List Bool
  square : (Nat.sqrt bits.length) ^ 2 = bits.length
  deriving DecidableEq

namespace Input

def side (input : Input) : Nat := Nat.sqrt input.bits.length

def sizes (input : Input) : List Nat :=
  List.replicate input.side input.side

def rows (input : Input) : List (List Bool) :=
  input.sizes.splitLengths input.bits

def delimitedRows (input : Input) : DelimitedBinaryWords.Input :=
  ⟨input.rows⟩

end Input

def decode (bits : List Bool) : Option Input :=
  if square : (Nat.sqrt bits.length) ^ 2 = bits.length then
    some ⟨bits, square⟩
  else
    none

@[simp] theorem decode_encode (input : Input) :
    decode input.bits = some input := by
  rcases input with ⟨bits, square⟩
  simp [decode, square]

noncomputable def finEncoding : _root_.Computability.FinEncoding Input where
  toEncoding :=
    { Γ := Bool
      encode := Input.bits
      decode := decode
      decode_encode := decode_encode }
  ΓFin := inferInstance

@[simp] theorem length_eq_side_sq (input : Input) :
    input.bits.length = input.side ^ 2 := input.square.symm

@[simp] theorem sizes_length (input : Input) :
    input.sizes.length = input.side := by
  simp [Input.sizes]

@[simp] theorem sizes_sum (input : Input) :
    input.sizes.sum = input.bits.length := by
  simp only [Input.sizes, List.sum_replicate]
  simpa only [Input.side, pow_two, Nat.nsmul_eq_mul] using input.square

@[simp] theorem rows_length (input : Input) :
    input.rows.length = input.side := by
  simp [Input.rows]

@[simp] theorem rows_flatten (input : Input) :
    input.rows.flatten = input.bits := by
  apply List.flatten_splitLengths
  exact (sizes_sum input).ge

@[simp] theorem rows_map_length (input : Input) :
    input.rows.map List.length = input.sizes := by
  apply List.map_splitLengths_length
  exact (sizes_sum input).le

theorem rows_forall_length (input : Input) :
    input.rows.Forall fun row => row.length = input.side := by
  rw [List.forall_iff_forall_mem]
  intro row rowMem
  have lengthMem : row.length ∈ input.rows.map List.length :=
    List.mem_map.mpr ⟨row, rowMem, rfl⟩
  rw [rows_map_length] at lengthMem
  exact List.eq_of_mem_replicate lengthMem

@[simp] theorem encodedRows_eq_encode (input : Input) :
    encodedRows input.rows =
      DelimitedBinaryWords.encode input.delimitedRows := by
  rfl

theorem bits_eq_nil_of_side_eq_zero (input : Input)
    (sideZero : input.side = 0) : input.bits = [] := by
  apply List.eq_nil_of_length_eq_zero
  rw [length_eq_side_sq, sideZero]
  simp

end BoolSquareRows
end LeanTrominoes

end
