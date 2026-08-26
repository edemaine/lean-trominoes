/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordEqualitySquareCompiler
import LeanTrominoes.DelimitedBinaryWordEqualitySquareSemantics
import LeanTrominoes.LastRepresentativeEqualityRowsTime
import LeanTrominoes.LastTrueUnaryValueLookupTime
import LeanTrominoes.ListDedupMapInjectiveOn
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2ForkMachineTime
import LeanTrominoes.TM2ListAppendClosure
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport
import LeanTrominoes.UnaryFieldBinaryWordCompiler
import LeanTrominoes.UnaryFieldEncoderFlatMapSemantics
import LeanTrominoes.UnaryPermutationRankLookupData

/-! # Polynomial-time unary lookup in permutation-rank order -/

noncomputable section

namespace LeanTrominoes
namespace UnaryPermutationRankLookup

open Computability Turing

private theorem word_injective :
    Function.Injective UnaryFieldBinaryWords.word := by
  intro first second equal
  have lengths := congrArg List.length equal
  simpa [UnaryFieldBinaryWords.word] using lengths

private theorem equalityRow_map_word (source : List Nat) (value : Nat) :
    LastRepresentativeEqualityRows.equalityRow
        (source.map UnaryFieldBinaryWords.word)
        (UnaryFieldBinaryWords.word value) =
      LastRepresentativeEqualityRows.equalityRow source value := by
  unfold LastRepresentativeEqualityRows.equalityRow
  rw [List.map_map]
  apply List.map_congr_left
  intro other _otherMember
  simp [word_injective.eq_iff]

theorem rankRows_eq_pipeline (ranks : List Nat) :
    DelimitedBinaryWordsFirstTrue.rows
        (LastRepresentativeEqualityRows.rows
          (DelimitedBinaryWordEqualitySquare.rows
            (UnaryFieldBinaryWords.words (extendedRanks ranks)))) =
      rankRows ranks := by
  rw [DelimitedBinaryWordEqualitySquare.rows_eq,
    LastRepresentativeEqualityRows.rows_equalityRows]
  unfold UnaryFieldBinaryWords.words
  rw [List.dedup_map_of_injective word_injective]
  unfold DelimitedBinaryWordsFirstTrue.rows rankRows
  congr 1
  simp only [List.map_map]
  apply List.map_congr_left
  intro rank _rankMember
  simp only [Function.comp_apply]
  rw [equalityRow_map_word]

/-- Append a canonical unary range to any compiled rank column. -/
noncomputable def extendedRanksComputableInPolyTime
    {Input InputSymbol : Type}
    [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeInput : Input → List InputSymbol)
    (ranks : Input → List Nat)
    (rankCompiler : TM2ComputableInPolyTime encodeInput
      UnaryFieldEncoderMachine.unaryFields ranks) :
    TM2ComputableInPolyTime encodeInput
      UnaryFieldEncoderMachine.unaryFields
      (fun input => extendedRanks (ranks input)) := by
  let rangeCompiler := TM2CompositionMachine.computableInPolyTime
    rankCompiler UnaryFieldRange.computableInPolyTime
  let rawRankCompiler :=
    TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
      (encodeOutput₂ := id)
      (function₂ := fun input =>
        UnaryFieldEncoderMachine.unaryFields (ranks input))
      rankCompiler (fun _ => rfl)
  let rawRangeCompiler :=
    TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
      (encodeOutput₂ := id)
      (function₂ := fun input => UnaryFieldEncoderMachine.unaryFields
        (UnaryFieldRange.values (ranks input)))
      rangeCompiler (fun _ => rfl)
  let appended := TM2ListAppend.computableInPolyTime
    rawRankCompiler rawRangeCompiler
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq appended
    (fun input => by
      change UnaryFieldEncoderMachine.unaryFields (ranks input) ++
          UnaryFieldEncoderMachine.unaryFields
            (UnaryFieldRange.values (ranks input)) =
        UnaryFieldEncoderMachine.unaryFields
          (ranks input ++ UnaryFieldRange.values (ranks input))
      rw [← UnaryFieldEncoderMachine.unaryFields_append])

/-- Compile the rank-ordered first-true equality rows. -/
noncomputable def rankRowsComputableInPolyTime
    {Input InputSymbol : Type}
    [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeInput : Input → List InputSymbol)
    (ranks : Input → List Nat)
    (rankCompiler : TM2ComputableInPolyTime encodeInput
      UnaryFieldEncoderMachine.unaryFields ranks) :
    TM2ComputableInPolyTime encodeInput
      DelimitedBinaryWords.finEncoding.encode
      (fun input => rankRows (ranks input)) := by
  let extendedCompiler := extendedRanksComputableInPolyTime
    encodeInput ranks rankCompiler
  let wordCompiler := TM2CompositionMachine.computableInPolyTime
    extendedCompiler UnaryFieldBinaryWords.wordsComputableInPolyTime
  let equalityCompiler :=
    DelimitedBinaryWordEqualitySquare.rowsComputableInPolyTime
      encodeInput
      (fun input => UnaryFieldBinaryWords.words
        (extendedRanks (ranks input))) wordCompiler
  let representativeCompiler := TM2CompositionMachine.computableInPolyTime
    equalityCompiler LastRepresentativeEqualityRowsMachine.computableInPolyTime
  let firstTrueCompiler := TM2CompositionMachine.computableInPolyTime
    representativeCompiler DelimitedBinaryWordsFirstTrue.computableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    firstTrueCompiler fun input => congrArg DelimitedBinaryWords.encode
      (rankRows_eq_pipeline (ranks input))

/-- Compile original field values followed by one zero per rank. -/
noncomputable def paddedValuesComputableInPolyTime
    {Input InputSymbol : Type}
    [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeInput : Input → List InputSymbol)
    (ranks fieldValues : Input → List Nat)
    (rankCompiler : TM2ComputableInPolyTime encodeInput
      UnaryFieldEncoderMachine.unaryFields ranks)
    (fieldCompiler : TM2ComputableInPolyTime encodeInput
      UnaryFieldEncoderMachine.unaryFields fieldValues) :
    TM2ComputableInPolyTime encodeInput
      UnaryFieldEncoderMachine.unaryFields
      (fun input => paddedValues (ranks input) (fieldValues input)) := by
  let zeroCompiler := TM2CompositionMachine.computableInPolyTime
    rankCompiler UnaryFieldConstantStreams.zerosComputableInPolyTime
  let rawFieldCompiler :=
    TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
      (encodeOutput₂ := id)
      (function₂ := fun input =>
        UnaryFieldEncoderMachine.unaryFields (fieldValues input))
      fieldCompiler (fun _ => rfl)
  let rawZeroCompiler :=
    TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
      (encodeOutput₂ := id)
      (function₂ := fun input => UnaryFieldEncoderMachine.unaryFields
        (UnaryFieldConstantStreams.zeros (ranks input)))
      zeroCompiler (fun _ => rfl)
  let appended := TM2ListAppend.computableInPolyTime
    rawFieldCompiler rawZeroCompiler
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq appended
    (fun input => by
      change UnaryFieldEncoderMachine.unaryFields (fieldValues input) ++
          UnaryFieldEncoderMachine.unaryFields
            (UnaryFieldConstantStreams.zeros (ranks input)) =
        UnaryFieldEncoderMachine.unaryFields
          (fieldValues input ++
            UnaryFieldConstantStreams.zeros (ranks input))
      rw [← UnaryFieldEncoderMachine.unaryFields_append])

local instance : Inhabited DelimitedBinaryWords.finEncoding.Γ :=
  ⟨DelimitedBinaryWords.Token.wordStart⟩

/-- Compile the promised row/value package consumed by unary lookup. -/
noncomputable def inputComputableInPolyTime
    {Input InputSymbol : Type}
    [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeInput : Input → List InputSymbol)
    (ranks fieldValues : Input → List Nat)
    (aligned : ∀ input, (fieldValues input).length = (ranks input).length)
    (rankCompiler : TM2ComputableInPolyTime encodeInput
      UnaryFieldEncoderMachine.unaryFields ranks)
    (fieldCompiler : TM2ComputableInPolyTime encodeInput
      UnaryFieldEncoderMachine.unaryFields fieldValues) :
    TM2ComputableInPolyTime encodeInput
      LastTrueUnaryValueLookupMachine.encode
      (fun source => input (ranks source) (fieldValues source)
        (aligned source)) := by
  let rowCompiler := rankRowsComputableInPolyTime
    encodeInput ranks rankCompiler
  let valueCompiler := paddedValuesComputableInPolyTime
    encodeInput ranks fieldValues rankCompiler fieldCompiler
  let paired := TM2ForkMachine.computableInPolyTime
    rowCompiler valueCompiler
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq paired
    (fun _ => rfl)

/-- Any aligned unary field column can be emitted in increasing rank order
when its ranks form a permutation; the compiler itself is total and does not
need the permutation promise. -/
noncomputable def valuesComputableInPolyTime
    {Input InputSymbol : Type}
    [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeInput : Input → List InputSymbol)
    (ranks fieldValues : Input → List Nat)
    (aligned : ∀ input, (fieldValues input).length = (ranks input).length)
    (rankCompiler : TM2ComputableInPolyTime encodeInput
      UnaryFieldEncoderMachine.unaryFields ranks)
    (fieldCompiler : TM2ComputableInPolyTime encodeInput
      UnaryFieldEncoderMachine.unaryFields fieldValues) :
    TM2ComputableInPolyTime encodeInput
      UnaryFieldEncoderMachine.unaryFields
      (fun source => values (ranks source) (fieldValues source)) := by
  let inputCompiler := inputComputableInPolyTime encodeInput ranks fieldValues
    aligned rankCompiler fieldCompiler
  let composed := TM2CompositionMachine.computableInPolyTime
    inputCompiler LastTrueUnaryValueLookupMachine.computableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq composed
    (fun _ => rfl)

end UnaryPermutationRankLookup
end LeanTrominoes

end
