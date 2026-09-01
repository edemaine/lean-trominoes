/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport
import LeanTrominoes.UnaryFieldEncoderFlatMapSemantics

/-! # Unary-field block maps from finite source alphabets -/

noncomputable section

namespace LeanTrominoes.FiniteUnaryFieldBlockMap

open Computability Turing

def values {Source : Type} (blockValues : Source → List Nat)
    (source : List Source) : List Nat :=
  source.flatMap blockValues

def block {Source : Type} (blockValues : Source → List Nat)
    (symbol : Source) : List UnaryFieldEncoderMachine.Symbol :=
  UnaryFieldEncoderMachine.unaryFields (blockValues symbol)

theorem flatMap_block_eq_unaryFields
    {Source : Type} (blockValues : Source → List Nat)
    (source : List Source) :
    source.flatMap (block blockValues) =
      UnaryFieldEncoderMachine.unaryFields
        (values blockValues source) := by
  induction source with
  | nil => rfl
  | cons symbol source induction =>
      change UnaryFieldEncoderMachine.unaryFields (blockValues symbol) ++
          source.flatMap (block blockValues) =
        UnaryFieldEncoderMachine.unaryFields
          (blockValues symbol ++ values blockValues source)
      rw [UnaryFieldEncoderMachine.unaryFields_append, induction]

/-- A fixed unary-field block for every symbol of a finite input alphabet is
polynomial-time computable. -/
noncomputable def computableInPolyTime
    {Source : Type} [Fintype Source]
    (blockValues : Source → List Nat) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (values blockValues) := by
  let physical : TM2ComputableInPolyTime id id
      (fun source : List Source => source.flatMap (block blockValues)) :=
    FiniteBlockTransducer.computableInPolyTime (block blockValues)
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq physical
    (flatMap_block_eq_unaryFields blockValues)

end LeanTrominoes.FiniteUnaryFieldBlockMap

end
