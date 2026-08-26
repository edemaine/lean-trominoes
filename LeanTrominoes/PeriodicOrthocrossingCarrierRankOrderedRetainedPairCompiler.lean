/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedPairCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedPairCrossoverCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedPairNextSliceCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedPairOwnershipCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedRetainedPairData

/-! # Compiler for sparse globally rank-ordered retained carrier pairs -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankOrderedPairs

open Computability Turing

noncomputable def nonCrossoverCandidateBitsComputableInPolyTime :
    TM2ComputableInPolyTime InputEncoding id nonCrossoverCandidateBits :=
  AlignedBooleanListClosure.combinedComputableInPolyTime
    InputEncoding .conjunction bits differentCrossoverBits
    (fun descriptors => by simp)
    bitsComputableInPolyTime differentCrossoverBitsComputableInPolyTime

noncomputable def retainedMaskBitsComputableInPolyTime :
    TM2ComputableInPolyTime InputEncoding id retainedMaskBits :=
  AlignedBooleanListClosure.combinedComputableInPolyTime
    InputEncoding .conjunction
    nonCrossoverCandidateBits representativeBits
    (fun descriptors => by simp)
    nonCrossoverCandidateBitsComputableInPolyTime
    representativeBitsComputableInPolyTime

noncomputable def retainedAxisBitsComputableInPolyTime :
    TM2ComputableInPolyTime InputEncoding id retainedAxisBits :=
  AlignedBooleanListClosure.combinedComputableInPolyTime
    InputEncoding .conjunction retainedMaskBits axisBits
    (fun descriptors => by simp [axisBits])
    retainedMaskBitsComputableInPolyTime axisBitsComputableInPolyTime

noncomputable def retainedNextSliceBitsComputableInPolyTime :
    TM2ComputableInPolyTime InputEncoding id retainedNextSliceBits :=
  AlignedBooleanListClosure.combinedComputableInPolyTime
    InputEncoding .conjunction retainedMaskBits nextSliceBits
    (fun descriptors => by simp)
    retainedMaskBitsComputableInPolyTime nextSliceBitsComputableInPolyTime

private noncomputable def retainedMaskValuesComputableInPolyTime :
    TM2ComputableInPolyTime InputEncoding
      UnaryFieldEncoderMachine.unaryFields
      (fun descriptors =>
        BooleanListUnaryFields.values (retainedMaskBits descriptors)) :=
  TM2CompositionMachine.computableInPolyTime
    retainedMaskBitsComputableInPolyTime
    BooleanListUnaryFields.valuesComputableInPolyTime

private noncomputable def retainedAxisValuesComputableInPolyTime :
    TM2ComputableInPolyTime InputEncoding
      UnaryFieldEncoderMachine.unaryFields
      (fun descriptors =>
        BooleanListUnaryFields.values (retainedAxisBits descriptors)) :=
  TM2CompositionMachine.computableInPolyTime
    retainedAxisBitsComputableInPolyTime
    BooleanListUnaryFields.valuesComputableInPolyTime

private noncomputable def retainedNextSliceValuesComputableInPolyTime :
    TM2ComputableInPolyTime InputEncoding
      UnaryFieldEncoderMachine.unaryFields
      (fun descriptors =>
        BooleanListUnaryFields.values
          (retainedNextSliceBits descriptors)) :=
  TM2CompositionMachine.computableInPolyTime
    retainedNextSliceBitsComputableInPolyTime
    BooleanListUnaryFields.valuesComputableInPolyTime

noncomputable def baseEmissionCodesComputableInPolyTime :
    TM2ComputableInPolyTime InputEncoding
      UnaryFieldEncoderMachine.unaryFields baseEmissionCodes :=
  AlignedUnaryListClosure.addedComputableInPolyTime
    InputEncoding
    (fun descriptors =>
      BooleanListUnaryFields.values (retainedMaskBits descriptors))
    (fun descriptors =>
      BooleanListUnaryFields.values (retainedAxisBits descriptors))
    (fun descriptors => by
      simp [BooleanListUnaryFields.values])
    retainedMaskValuesComputableInPolyTime
    retainedAxisValuesComputableInPolyTime

noncomputable def doubledNextSliceCodesComputableInPolyTime :
    TM2ComputableInPolyTime InputEncoding
      UnaryFieldEncoderMachine.unaryFields doubledNextSliceCodes :=
  AlignedUnaryListClosure.addedComputableInPolyTime
    InputEncoding
    (fun descriptors =>
      BooleanListUnaryFields.values
        (retainedNextSliceBits descriptors))
    (fun descriptors =>
      BooleanListUnaryFields.values
        (retainedNextSliceBits descriptors))
    (fun _ => rfl)
    retainedNextSliceValuesComputableInPolyTime
    retainedNextSliceValuesComputableInPolyTime

noncomputable def emissionCodesComputableInPolyTime :
    TM2ComputableInPolyTime InputEncoding
      UnaryFieldEncoderMachine.unaryFields emissionCodes :=
  AlignedUnaryListClosure.addedComputableInPolyTime
    InputEncoding baseEmissionCodes doubledNextSliceCodes
    (fun descriptors => by simp)
    baseEmissionCodesComputableInPolyTime
    doubledNextSliceCodesComputableInPolyTime

/-- The exact sparse retained carrier-pair bit stream is polynomial-time
computable from numeric route descriptors. -/
noncomputable def retainedPairBitsComputableInPolyTime :
    TM2ComputableInPolyTime InputEncoding id retainedPairBits := by
  let composed := TM2CompositionMachine.computableInPolyTime
    emissionCodesComputableInPolyTime
    UnaryCarrierPairBits.pairsComputableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    composed (fun _ => rfl)

end CarrierRankOrderedPairs
end LeanTrominoes.PeriodicOrthocrossing

end
