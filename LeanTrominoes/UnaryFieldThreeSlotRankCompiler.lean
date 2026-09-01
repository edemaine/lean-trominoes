/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.TM2PolyTimeInputEncodingTransport
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport
import LeanTrominoes.UnaryFieldEncoderFlatMapSemantics
import LeanTrominoes.UnaryFieldEncoderMachine

/-! # Three fixed slot ranks per unary field -/

noncomputable section

namespace LeanTrominoes.UnaryFieldThreeSlotRanks

open Computability Turing

abbrev Symbol := UnaryFieldEncoderMachine.Symbol

/-- Emit red/green/blue slot numbers beside every source field. -/
def values (source : List Nat) : List Nat :=
  source.flatMap fun _ => [0, 1, 2]

def block : Symbol → List Symbol
  | .unit => []
  | .delimiter => UnaryFieldEncoderMachine.unaryFields [0, 1, 2]

def tokens (source : List Symbol) : List Symbol :=
  source.flatMap block

@[simp] theorem flatMap_block_unaryField (value : Nat) :
    (UnaryFieldEncoderMachine.unaryField value).flatMap block =
      UnaryFieldEncoderMachine.unaryFields [0, 1, 2] := by
  simp [UnaryFieldEncoderMachine.unaryField, block]

@[simp] theorem tokens_unaryFields (source : List Nat) :
    tokens (UnaryFieldEncoderMachine.unaryFields source) =
      UnaryFieldEncoderMachine.unaryFields (values source) := by
  unfold tokens values
  induction source with
  | nil => rfl
  | cons value source induction =>
      rw [UnaryFieldEncoderMachine.unaryFields_cons,
        List.flatMap_append, flatMap_block_unaryField, induction,
        List.flatMap_cons, UnaryFieldEncoderMachine.unaryFields_append]

/-- Ignoring each unary body and expanding its delimiter into the three
fixed slot fields is linear-time. -/
noncomputable def computableInPolyTime :
    TM2ComputableInPolyTime
      UnaryFieldEncoderMachine.unaryFields
      UnaryFieldEncoderMachine.unaryFields values := by
  let mapped := FiniteBlockTransducer.computableInPolyTime block
  let physical : TM2ComputableInPolyTime
      UnaryFieldEncoderMachine.unaryFields id
      (fun source => tokens
        (UnaryFieldEncoderMachine.unaryFields source)) :=
    TM2PolyTimeInputEncodingTransport.of_prepare
      UnaryFieldEncoderMachine.unaryFields mapped
      (fun _ => rfl) (fun _ => rfl)
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    physical tokens_unaryFields

end LeanTrominoes.UnaryFieldThreeSlotRanks

end
