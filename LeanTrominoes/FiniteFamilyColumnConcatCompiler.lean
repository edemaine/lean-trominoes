/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordsAppendClosure
import LeanTrominoes.UnaryFieldEncoderAppendClosure
import LeanTrominoes.FiniteBlockTransducer

/-! # Concatenating a fixed finite family of compiled columns -/

noncomputable section
namespace LeanTrominoes
open Computability Turing

namespace DelimitedBinaryWords

/-- The family index list is fixed independently of the machine input. -/
noncomputable def flatMapComputableInPolyTime
    {Index InputSymbol : Type} [Fintype InputSymbol]
    (indices : List Index) (family : Index → List InputSymbol → Input)
    (compiled : ∀ index, TM2ComputableInPolyTime id finEncoding.encode (family index)) :
    TM2ComputableInPolyTime id finEncoding.encode
      (fun input => ⟨indices.flatMap fun index => (family index input).words⟩) := by
  induction indices with
  | nil =>
      exact TM2PolyTimeOutputEncodingTransport.of_identity_output_eq
        (FiniteBlockTransducer.computableInPolyTime (fun _ : InputSymbol => ([] : List Token)))
        (fun input => by
          change input.flatMap (fun _ => ([] : List Token)) = []
          induction input <;> simp_all)
  | cons index indices induction =>
      exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
        (appendComputableInPolyTime (compiled index) induction)
        (fun input => rfl)

end DelimitedBinaryWords
namespace UnaryFieldEncoderMachine

/-- Concatenation of finitely many unary columns preserves their family order. -/
noncomputable def flatMapComputableInPolyTime
    {Index InputSymbol : Type} [Fintype InputSymbol]
    (indices : List Index) (family : Index → List InputSymbol → List Nat)
    (compiled : ∀ index, TM2ComputableInPolyTime id unaryFields (family index)) :
    TM2ComputableInPolyTime id unaryFields
      (fun input => indices.flatMap fun index => family index input) := by
  induction indices with
  | nil =>
      exact TM2PolyTimeOutputEncodingTransport.of_identity_output_eq
        (FiniteBlockTransducer.computableInPolyTime (fun _ : InputSymbol => ([] : List Symbol)))
        (fun input => by simp [unaryFields])
  | cons index indices induction =>
      exact appendComputableInPolyTime (compiled index) induction

end UnaryFieldEncoderMachine
end LeanTrominoes
end
