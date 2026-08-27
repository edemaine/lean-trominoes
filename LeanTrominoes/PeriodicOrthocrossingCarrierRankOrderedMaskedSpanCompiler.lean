/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedMaskedSpanData
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedPairSpanCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedRetainedPairCompiler
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2ForkMachineTime
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport
import LeanTrominoes.UnarySuccessorEqualityFilterTime

/-! # Compiler for axis-masked retained carrier spans -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankOrderedPairs

open Computability Turing

noncomputable def maskedSpanCodesComputableInPolyTime
    {Input InputSymbol : Type}
    [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeInput : Input → List InputSymbol)
    (spans : Input → List Nat) (mask : Input → List Bool)
    (lengthEq : ∀ input, (spans input).length = (mask input).length)
    (spansCompiler :
      @TM2ComputableInPolyTime
        Input (List Nat) InputSymbol UnaryFieldEncoderMachine.Symbol
        encodeInput UnaryFieldEncoderMachine.unaryFields spans)
    (maskCompiler :
      @TM2ComputableInPolyTime
        Input (List Bool) InputSymbol Bool encodeInput id mask) :
    @TM2ComputableInPolyTime
      Input (List Nat) InputSymbol UnaryFieldEncoderMachine.Symbol
      encodeInput UnaryFieldEncoderMachine.unaryFields
      (fun input => maskedSpanCodes (spans input) (mask input)) := by
  let ranksCompiler := TM2CompositionMachine.computableInPolyTime
    spansCompiler (UnaryFieldConstantOffsets.computableInPolyTime 1)
  let baseSizesCompiler := TM2CompositionMachine.computableInPolyTime
    spansCompiler (UnaryFieldConstantOffsets.computableInPolyTime 2)
  let inactiveBitsCompiler :=
    AlignedBooleanListClosure.mapNegatedComputableInPolyTime
      encodeInput mask maskCompiler
  let inactiveValuesCompiler := TM2CompositionMachine.computableInPolyTime
    inactiveBitsCompiler BooleanListUnaryFields.valuesComputableInPolyTime
  let sizesCompiler := AlignedUnaryListClosure.addedComputableInPolyTime
    encodeInput
    (fun input => spanFilterBaseSizes (spans input))
    (fun input => inactiveMaskValues (mask input))
    (fun input => by simp [lengthEq input])
    baseSizesCompiler inactiveValuesCompiler
  let paired := TM2ForkMachine.computableInPolyTime
    ranksCompiler sizesCompiler
  let prepared : TM2ComputableInPolyTime encodeInput
      UnarySuccessorEqualityFilterMachine.encode
      (fun input => spanFilterInput
        (spans input) (mask input) (lengthEq input)) :=
    TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
      paired (fun _ => rfl)
  let composed := TM2CompositionMachine.computableInPolyTime prepared
    UnarySuccessorEqualityFilterMachine.computableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    composed (fun _ => rfl)

noncomputable def verticalMaskBitsComputableInPolyTime :
    TM2ComputableInPolyTime InputEncoding id verticalMaskBits := by
  let notAxisCompiler :=
    AlignedBooleanListClosure.mapNegatedComputableInPolyTime
      InputEncoding axisBits axisBitsComputableInPolyTime
  exact AlignedBooleanListClosure.combinedComputableInPolyTime
    InputEncoding .conjunction retainedMaskBits
    (fun descriptors =>
      AlignedBooleanListClosure.negated (axisBits descriptors))
    (fun descriptors => by simp [axisBits])
    retainedMaskBitsComputableInPolyTime notAxisCompiler

/-- Retained horizontal span codes are polynomial-time computable. -/
noncomputable def horizontalSpanCodesComputableInPolyTime :
    TM2ComputableInPolyTime InputEncoding
      UnaryFieldEncoderMachine.unaryFields horizontalSpanCodes :=
  maskedSpanCodesComputableInPolyTime
    InputEncoding orderSpans retainedAxisBits
    (fun descriptors => by simp)
    orderSpansComputableInPolyTime
    retainedAxisBitsComputableInPolyTime

/-- Retained vertical span codes are polynomial-time computable. -/
noncomputable def verticalSpanCodesComputableInPolyTime :
    TM2ComputableInPolyTime InputEncoding
      UnaryFieldEncoderMachine.unaryFields verticalSpanCodes :=
  maskedSpanCodesComputableInPolyTime
    InputEncoding orderSpans verticalMaskBits
    (fun descriptors => by simp)
    orderSpansComputableInPolyTime
    verticalMaskBitsComputableInPolyTime

end CarrierRankOrderedPairs
end LeanTrominoes.PeriodicOrthocrossing

end
