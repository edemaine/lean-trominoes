/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairExcessTime
import LeanTrominoes.DelimitedBinaryWordPairProductTime
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumCompiledRankOrderedFieldCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedPairData
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Compiler for candidate pairs over globally rank-ordered carrier data -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankOrderedPairs

open Computability Turing
open CarrierRankDatumCompiledFields

noncomputable def fieldEqualityBitsComputableInPolyTime
    (field : CarrierRankDatumCompiledFields.Field) :
    TM2ComputableInPolyTime InputEncoding id (fieldEqualityBits field) :=
  UnaryFieldEqualityRows.equalityBitsComputableInPolyTime
    InputEncoding field.rankOrderedValues
    field.rankOrderedValuesComputableInPolyTime

noncomputable def horizontalTranslationEqualityBitsComputableInPolyTime :
    TM2ComputableInPolyTime InputEncoding id
      horizontalTranslationEqualityBits :=
  SignedUnaryEquality.equalityBitsComputableInPolyTime
    InputEncoding
    (Field.rankOrderedValues .keyTranslateHorizontalPositive)
    (Field.rankOrderedValues .keyTranslateHorizontalNegative)
    (rankOrderedValues_lengths_eq _ _)
    (Field.rankOrderedValuesComputableInPolyTime
      .keyTranslateHorizontalPositive)
    (Field.rankOrderedValuesComputableInPolyTime
      .keyTranslateHorizontalNegative)

noncomputable def verticalTranslationEqualityBitsComputableInPolyTime :
    TM2ComputableInPolyTime InputEncoding id verticalTranslationEqualityBits :=
  SignedUnaryEquality.equalityBitsComputableInPolyTime
    InputEncoding
    (Field.rankOrderedValues .keyTranslateVerticalPositive)
    (Field.rankOrderedValues .keyTranslateVerticalNegative)
    (rankOrderedValues_lengths_eq _ _)
    (Field.rankOrderedValuesComputableInPolyTime
      .keyTranslateVerticalPositive)
    (Field.rankOrderedValuesComputableInPolyTime
      .keyTranslateVerticalNegative)

noncomputable def indexEqualityBitsComputableInPolyTime :
    TM2ComputableInPolyTime InputEncoding id indexEqualityBits :=
  AlignedBooleanListClosure.combinedComputableInPolyTime
    InputEncoding .conjunction
    (fieldEqualityBits .keyRoute) (fieldEqualityBits .keySegment)
    (fun descriptors => by simp)
    (fieldEqualityBitsComputableInPolyTime .keyRoute)
    (fieldEqualityBitsComputableInPolyTime .keySegment)

noncomputable def translationEqualityBitsComputableInPolyTime :
    TM2ComputableInPolyTime InputEncoding id translationEqualityBits :=
  AlignedBooleanListClosure.combinedComputableInPolyTime
    InputEncoding .conjunction
    horizontalTranslationEqualityBits verticalTranslationEqualityBits
    (fun descriptors => by
      simp [horizontalTranslationEqualityBits,
        verticalTranslationEqualityBits])
    horizontalTranslationEqualityBitsComputableInPolyTime
    verticalTranslationEqualityBitsComputableInPolyTime

noncomputable def sameKeyBitsComputableInPolyTime :
    TM2ComputableInPolyTime InputEncoding id sameKeyBits :=
  AlignedBooleanListClosure.combinedComputableInPolyTime
    InputEncoding .conjunction indexEqualityBits translationEqualityBits
    (fun descriptors => by simp)
    indexEqualityBitsComputableInPolyTime
    translationEqualityBitsComputableInPolyTime

noncomputable def positionsComputableInPolyTime :
    TM2ComputableInPolyTime InputEncoding
      UnaryFieldEncoderMachine.unaryFields positions := by
  let composed := TM2CompositionMachine.computableInPolyTime
    (Field.rankOrderedValuesComputableInPolyTime .keyRoute)
    UnaryFieldRange.computableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    composed (fun _ => rfl)

noncomputable def successorBitsComputableInPolyTime :
    TM2ComputableInPolyTime InputEncoding id successorBits := by
  let wordCompiler := TM2CompositionMachine.computableInPolyTime
    positionsComputableInPolyTime
    UnaryFieldBinaryWords.wordsComputableInPolyTime
  let pairCompilerRaw := TM2CompositionMachine.computableInPolyTime
    wordCompiler DelimitedBinaryWordPairProductMachine.computableInPolyTime
  let pairCompiler : TM2ComputableInPolyTime InputEncoding
      DelimitedBinaryWordPairs.finEncoding.encode positionWordPairs :=
    TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
      pairCompilerRaw (fun _ => rfl)
  let excessCompilerRaw := TM2CompositionMachine.computableInPolyTime
    pairCompiler
    (DelimitedBinaryWordPairExcessMachine.computableInPolyTime false)
  let excessCompiler : TM2ComputableInPolyTime InputEncoding
      UnaryFieldEncoderMachine.unaryFields positionExcesses :=
    TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
      excessCompilerRaw (fun _ => rfl)
  let composed := TM2CompositionMachine.computableInPolyTime
    excessCompiler UnaryExactOneBooleans.bitsComputableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    composed (fun _ => rfl)

/-- Candidate carrier pairs in exact global-rank order are polynomial-time
computable from the numeric route descriptors. -/
noncomputable def bitsComputableInPolyTime :
    TM2ComputableInPolyTime InputEncoding id bits :=
  AlignedBooleanListClosure.combinedComputableInPolyTime
    InputEncoding .conjunction sameKeyBits successorBits
    (fun descriptors => by simp)
    sameKeyBitsComputableInPolyTime successorBitsComputableInPolyTime

end CarrierRankOrderedPairs
end LeanTrominoes.PeriodicOrthocrossing

end
