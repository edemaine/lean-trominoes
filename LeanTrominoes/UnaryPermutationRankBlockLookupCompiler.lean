/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordFixedFieldRowExpansionCompiler
import LeanTrominoes.DelimitedBinaryWordFixedFieldRowExpansionSemantics
import LeanTrominoes.LastTrueUnaryValueLookupTime
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2ForkMachineTime
import LeanTrominoes.TM2ListAppendClosure
import LeanTrominoes.TM2PolyTimeInputEncodingTransport
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport
import LeanTrominoes.UnaryPermutationRankBlockLookupInput
import LeanTrominoes.UnaryPermutationRankLookupCompiler

/-! # Polynomial-time fixed-width permutation-rank block lookup -/

noncomputable section

namespace LeanTrominoes
namespace UnaryPermutationRankBlockLookup

open Computability Turing

local instance : Inhabited DelimitedBinaryWords.finEncoding.Γ :=
  ⟨DelimitedBinaryWords.Token.wordStart⟩

/-- Compile the rank rows expanded once per fixed-width block field. -/
noncomputable def expandedRowsComputableInPolyTime
    {Input InputSymbol : Type}
    [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeInput : Input → List InputSymbol)
    (width : Nat) (ranks : Input → List Nat)
    (rankCompiler : TM2ComputableInPolyTime encodeInput
      UnaryFieldEncoderMachine.unaryFields ranks) :
    TM2ComputableInPolyTime encodeInput
      DelimitedBinaryWords.finEncoding.encode
      (fun source => expandedRows width (ranks source)) := by
  let expander := TM2PolyTimeInputEncodingTransport.of_prepare
    DelimitedBinaryWords.encode
    (DelimitedBinaryWordFixedFieldRowExpansion.tokensComputableInPolyTime
      width)
    (fun _ => rfl) (fun _ => rfl)
  let compiled := TM2CompositionMachine.computableInPolyTime
    (UnaryPermutationRankLookup.rankRowsComputableInPolyTime
      encodeInput ranks rankCompiler)
    expander
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq compiled
    (fun source => by
      exact DelimitedBinaryWordFixedFieldRowExpansion.tokens_encode width
        (UnaryPermutationRankLookup.rankRows (ranks source)))

/-- Compile original fixed-width blocks followed by an equal-length zero
field stream. -/
noncomputable def paddedValuesComputableInPolyTime
    {Input InputSymbol : Type}
    [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeInput : Input → List InputSymbol)
    (fieldValues : Input → List Nat)
    (fieldCompiler : TM2ComputableInPolyTime encodeInput
      UnaryFieldEncoderMachine.unaryFields fieldValues) :
    TM2ComputableInPolyTime encodeInput
      UnaryFieldEncoderMachine.unaryFields
      (fun source => paddedValues (fieldValues source)) := by
  let zeroCompiler := TM2CompositionMachine.computableInPolyTime
    fieldCompiler UnaryFieldConstantStreams.zerosComputableInPolyTime
  let rawFieldCompiler :=
    TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
      (encodeOutput₂ := id)
      (function₂ := fun source =>
        UnaryFieldEncoderMachine.unaryFields (fieldValues source))
      fieldCompiler (fun _ => rfl)
  let rawZeroCompiler :=
    TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
      (encodeOutput₂ := id)
      (function₂ := fun source => UnaryFieldEncoderMachine.unaryFields
        (UnaryFieldConstantStreams.zeros (fieldValues source)))
      zeroCompiler (fun _ => rfl)
  let appended := TM2ListAppend.computableInPolyTime
    rawFieldCompiler rawZeroCompiler
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq appended
    (fun source => by
      change UnaryFieldEncoderMachine.unaryFields (fieldValues source) ++
          UnaryFieldEncoderMachine.unaryFields
            (UnaryFieldConstantStreams.zeros (fieldValues source)) =
        UnaryFieldEncoderMachine.unaryFields
          (paddedValues (fieldValues source))
      rw [← UnaryFieldEncoderMachine.unaryFields_append]
      rfl)

/-- Compile the promised row/value package consumed by unary lookup. -/
noncomputable def inputComputableInPolyTime
    {Input InputSymbol : Type}
    [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeInput : Input → List InputSymbol)
    (width : Nat) (ranks fieldValues : Input → List Nat)
    (aligned : ∀ source,
      (fieldValues source).length = (ranks source).length * width)
    (rankCompiler : TM2ComputableInPolyTime encodeInput
      UnaryFieldEncoderMachine.unaryFields ranks)
    (fieldCompiler : TM2ComputableInPolyTime encodeInput
      UnaryFieldEncoderMachine.unaryFields fieldValues) :
    TM2ComputableInPolyTime encodeInput
      LastTrueUnaryValueLookupMachine.encode
      (fun source => input width (ranks source) (fieldValues source)
        (aligned source)) := by
  let rowCompiler := expandedRowsComputableInPolyTime
    encodeInput width ranks rankCompiler
  let valueCompiler := paddedValuesComputableInPolyTime
    encodeInput fieldValues fieldCompiler
  let paired := TM2ForkMachine.computableInPolyTime
    rowCompiler valueCompiler
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq paired
    (fun _ => rfl)

/-- Any aligned fixed-width unary block column can be emitted in increasing
rank order when its ranks form a permutation; the compiler itself is total. -/
noncomputable def valuesComputableInPolyTime
    {Input InputSymbol : Type}
    [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeInput : Input → List InputSymbol)
    (width : Nat) (ranks fieldValues : Input → List Nat)
    (aligned : ∀ source,
      (fieldValues source).length = (ranks source).length * width)
    (rankCompiler : TM2ComputableInPolyTime encodeInput
      UnaryFieldEncoderMachine.unaryFields ranks)
    (fieldCompiler : TM2ComputableInPolyTime encodeInput
      UnaryFieldEncoderMachine.unaryFields fieldValues) :
    TM2ComputableInPolyTime encodeInput
      UnaryFieldEncoderMachine.unaryFields
      (fun source => values width (ranks source) (fieldValues source)) := by
  let inputCompiler := inputComputableInPolyTime encodeInput width
    ranks fieldValues aligned rankCompiler fieldCompiler
  let composed := TM2CompositionMachine.computableInPolyTime
    inputCompiler LastTrueUnaryValueLookupMachine.computableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq composed
    (fun _ => rfl)

end UnaryPermutationRankBlockLookup
end LeanTrominoes

end
