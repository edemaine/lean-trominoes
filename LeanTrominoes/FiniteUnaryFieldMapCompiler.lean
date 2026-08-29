/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport
import LeanTrominoes.UnaryFieldEncoderMachine

/-! # Unary-field maps from finite source alphabets -/

noncomputable section

namespace LeanTrominoes.FiniteUnaryFieldMap

open Computability Turing

def values {Source : Type} (value : Source → Nat)
    (source : List Source) : List Nat :=
  source.map value

def block {Source : Type} (value : Source → Nat)
    (symbol : Source) : List UnaryFieldEncoderMachine.Symbol :=
  UnaryFieldEncoderMachine.unaryField (value symbol)

theorem flatMap_block_eq_unaryFields
    {Source : Type} (value : Source → Nat)
    (source : List Source) :
    source.flatMap (block value) =
      UnaryFieldEncoderMachine.unaryFields (values value source) := by
  induction source with
  | nil => rfl
  | cons symbol source induction =>
      change block value symbol ++ source.flatMap (block value) =
        UnaryFieldEncoderMachine.unaryField (value symbol) ++
          UnaryFieldEncoderMachine.unaryFields (values value source)
      rw [induction]
      rfl

/-- Mapping any fixed natural-valued function over a finite source alphabet
and emitting the results as unary fields is polynomial time. -/
noncomputable def computableInPolyTime
    {Source : Type} [Fintype Source]
    (value : Source → Nat) :
    TM2ComputableInPolyTime id
      UnaryFieldEncoderMachine.unaryFields (values value) := by
  let physical : TM2ComputableInPolyTime id id
      (fun source : List Source => source.flatMap (block value)) :=
    FiniteBlockTransducer.computableInPolyTime (block value)
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq physical
    (flatMap_block_eq_unaryFields value)

end LeanTrominoes.FiniteUnaryFieldMap

end
