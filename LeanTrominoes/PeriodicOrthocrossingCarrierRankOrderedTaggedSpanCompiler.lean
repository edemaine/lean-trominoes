/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedMaskedSpanCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedTaggedSpanData

/-! # Compiler for axis-tagged retained carrier spans -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankOrderedPairs

open Computability Turing

noncomputable def doubledOrderSpansComputableInPolyTime :
    TM2ComputableInPolyTime InputEncoding
      UnaryFieldEncoderMachine.unaryFields doubledOrderSpans :=
  AlignedUnaryListClosure.addedComputableInPolyTime
    InputEncoding orderSpans orderSpans (fun _ => rfl)
    orderSpansComputableInPolyTime orderSpansComputableInPolyTime

noncomputable def maskedDoubledSpanCodesComputableInPolyTime :
    TM2ComputableInPolyTime InputEncoding
      UnaryFieldEncoderMachine.unaryFields maskedDoubledSpanCodes :=
  maskedSpanCodesComputableInPolyTime
    InputEncoding doubledOrderSpans retainedMaskBits
    (fun descriptors => by simp)
    doubledOrderSpansComputableInPolyTime
    retainedMaskBitsComputableInPolyTime

private noncomputable def retainedAxisValuesComputableInPolyTime :
    TM2ComputableInPolyTime InputEncoding
      UnaryFieldEncoderMachine.unaryFields
      (fun descriptors =>
        BooleanListUnaryFields.values (retainedAxisBits descriptors)) :=
  TM2CompositionMachine.computableInPolyTime
    retainedAxisBitsComputableInPolyTime
    BooleanListUnaryFields.valuesComputableInPolyTime

/-- The sparse tagged span stream is polynomial-time computable in original
global carrier-pair order. -/
noncomputable def taggedSpanCodesComputableInPolyTime :
    TM2ComputableInPolyTime InputEncoding
      UnaryFieldEncoderMachine.unaryFields taggedSpanCodes :=
  AlignedUnaryListClosure.addedComputableInPolyTime
    InputEncoding maskedDoubledSpanCodes
    (fun descriptors =>
      BooleanListUnaryFields.values (retainedAxisBits descriptors))
    (fun descriptors => by simp [BooleanListUnaryFields.values])
    maskedDoubledSpanCodesComputableInPolyTime
    retainedAxisValuesComputableInPolyTime

end CarrierRankOrderedPairs
end LeanTrominoes.PeriodicOrthocrossing

end
