/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedPackedSpanData
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedRetainedPairCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedTaggedSpanCompiler

/-! # Compiler for axis/next-slice-packed retained carrier spans -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankOrderedPairs

open Computability Turing

noncomputable def doubledTaggedSpanCodesComputableInPolyTime :
    TM2ComputableInPolyTime InputEncoding
      UnaryFieldEncoderMachine.unaryFields doubledTaggedSpanCodes :=
  AlignedUnaryListClosure.addedComputableInPolyTime
    InputEncoding taggedSpanCodes taggedSpanCodes (fun _ => rfl)
    taggedSpanCodesComputableInPolyTime taggedSpanCodesComputableInPolyTime

private noncomputable def retainedNextSliceValuesComputableInPolyTime :
    TM2ComputableInPolyTime InputEncoding
      UnaryFieldEncoderMachine.unaryFields
      (fun descriptors =>
        BooleanListUnaryFields.values
          (retainedNextSliceBits descriptors)) :=
  TM2CompositionMachine.computableInPolyTime
    retainedNextSliceBitsComputableInPolyTime
    BooleanListUnaryFields.valuesComputableInPolyTime

/-- The packed retained carrier-span stream is polynomial-time computable in
the original row-major pair order. -/
noncomputable def packedSpanCodesComputableInPolyTime :
    TM2ComputableInPolyTime InputEncoding
      UnaryFieldEncoderMachine.unaryFields packedSpanCodes :=
  AlignedUnaryListClosure.addedComputableInPolyTime
    InputEncoding doubledTaggedSpanCodes
    (fun descriptors =>
      BooleanListUnaryFields.values
        (retainedNextSliceBits descriptors))
    (fun descriptors => by simp [BooleanListUnaryFields.values])
    doubledTaggedSpanCodesComputableInPolyTime
    retainedNextSliceValuesComputableInPolyTime

end CarrierRankOrderedPairs
end LeanTrominoes.PeriodicOrthocrossing

end
