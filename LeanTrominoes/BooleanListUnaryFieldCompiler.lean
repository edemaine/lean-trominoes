/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport
import LeanTrominoes.UnaryFieldEncoderMachine

/-! # Boolean lists as zero-or-one unary fields -/

noncomputable section

namespace LeanTrominoes
namespace BooleanListUnaryFields

open Computability Turing

def bitNat : Bool → Nat
  | false => 0
  | true => 1

def values (bits : List Bool) : List Nat :=
  bits.map bitNat

def block : Bool → List UnaryFieldEncoderMachine.Symbol
  | false => [.delimiter]
  | true => [.unit, .delimiter]

def tokens (bits : List Bool) : List UnaryFieldEncoderMachine.Symbol :=
  bits.flatMap block

theorem tokens_eq_unaryFields (bits : List Bool) :
    tokens bits = UnaryFieldEncoderMachine.unaryFields (values bits) := by
  induction bits with
  | nil => rfl
  | cons bit bits induction =>
      change block bit ++ tokens bits =
        UnaryFieldEncoderMachine.unaryField (bitNat bit) ++
          UnaryFieldEncoderMachine.unaryFields (values bits)
      rw [induction]
      cases bit <;> rfl

/-- Re-encoding one Boolean per zero-or-one unary field is a fixed block
transduction and therefore polynomial-time. -/
noncomputable def valuesComputableInPolyTime :
    TM2ComputableInPolyTime id
      UnaryFieldEncoderMachine.unaryFields values := by
  let physical : TM2ComputableInPolyTime id id tokens :=
    FiniteBlockTransducer.computableInPolyTime block
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (encodeOutput₂ := UnaryFieldEncoderMachine.unaryFields)
    (function₂ := values) physical tokens_eq_unaryFields

end BooleanListUnaryFields
end LeanTrominoes

end
