/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.TM2PolyTimeInputEncodingTransport
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport
import LeanTrominoes.UnaryFieldEncoderMachine

/-! # Multiplying every unary field by a fixed constant -/

noncomputable section

namespace LeanTrominoes.UnaryFieldConstantScale

open Computability Turing

abbrev Symbol := UnaryFieldEncoderMachine.Symbol

def values (factor : Nat) (source : List Nat) : List Nat :=
  source.map fun value => value * factor

def block (factor : Nat) : Symbol → List Symbol
  | .unit => List.replicate factor .unit
  | .delimiter => [.delimiter]

private theorem flatMap_units (factor value : Nat) :
    (List.replicate value UnaryFieldEncoderMachine.Symbol.unit).flatMap
        (block factor) =
      List.replicate (value * factor)
        UnaryFieldEncoderMachine.Symbol.unit := by
  induction value with
  | zero => simp
  | succ value induction =>
      rw [List.replicate_succ, List.flatMap_cons, block, induction,
        ← List.replicate_add]
      simp [Nat.succ_mul, Nat.add_comm]

theorem flatMap_unaryField (factor value : Nat) :
    (UnaryFieldEncoderMachine.unaryField value).flatMap (block factor) =
      UnaryFieldEncoderMachine.unaryField (value * factor) := by
  unfold UnaryFieldEncoderMachine.unaryField
  rw [List.flatMap_append, flatMap_units]
  rfl

theorem flatMap_unaryFields (factor : Nat) (source : List Nat) :
    (UnaryFieldEncoderMachine.unaryFields source).flatMap (block factor) =
      UnaryFieldEncoderMachine.unaryFields (values factor source) := by
  induction source with
  | nil => rfl
  | cons value source induction =>
      rw [UnaryFieldEncoderMachine.unaryFields_cons, List.flatMap_append,
        flatMap_unaryField, induction]
      rfl

/-- Scaling unary fields by any fixed natural factor is linear-time. -/
noncomputable def computableInPolyTime (factor : Nat) :
    TM2ComputableInPolyTime UnaryFieldEncoderMachine.unaryFields
      UnaryFieldEncoderMachine.unaryFields (values factor) := by
  let physical :=
    FiniteBlockTransducer.computableInPolyTime (block factor)
  let prepared : TM2ComputableInPolyTime
      UnaryFieldEncoderMachine.unaryFields id
      (fun source =>
        (UnaryFieldEncoderMachine.unaryFields source).flatMap
          (block factor)) :=
    TM2PolyTimeInputEncodingTransport.of_prepare
      UnaryFieldEncoderMachine.unaryFields physical
      (fun _ => rfl) (fun _ => rfl)
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq prepared
    (flatMap_unaryFields factor)

end LeanTrominoes.UnaryFieldConstantScale

end
