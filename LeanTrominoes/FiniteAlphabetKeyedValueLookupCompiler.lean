/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.AlignedBooleanListClosure
import LeanTrominoes.DelimitedBinaryWordBooleanFilterCompiler
import LeanTrominoes.DelimitedBinaryWordEqualitySquareCompiler
import LeanTrominoes.DelimitedBinaryWordLengthsCompiler
import LeanTrominoes.DelimitedBinaryWordPairSecondWordsCompiler
import LeanTrominoes.FiniteAlphabetKeyedValueLookupData
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.FiniteUnaryFieldMapCompiler
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2ForkMachineTime
import LeanTrominoes.TM2ListAppendClosure
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport
import LeanTrominoes.UnaryFieldConstantStreamCompiler
import LeanTrominoes.UnaryFieldEncoderFlatMapSemantics

/-! # Compiler for keyed finite-alphabet value selection -/

noncomputable section

namespace LeanTrominoes.FiniteAlphabetKeyedValueLookup

open Computability Turing

variable {Value : Type} [Fintype Value] [Nonempty Value]

private noncomputable def appendUnaryComputableInPolyTime
    {Source InputSymbol : Type}
    [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeSource : Source → List InputSymbol)
    (first second : Source → List Nat)
    (firstCompiler : TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields first)
    (secondCompiler : TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields second) :
    TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields
      (fun source => first source ++ second source) := by
  let firstTokens : TM2ComputableInPolyTime encodeSource id
      (fun source => UnaryFieldEncoderMachine.unaryFields (first source)) :=
    TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
      firstCompiler (fun _ => rfl)
  let secondTokens : TM2ComputableInPolyTime encodeSource id
      (fun source => UnaryFieldEncoderMachine.unaryFields (second source)) :=
    TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
      secondCompiler (fun _ => rfl)
  let appended := TM2ListAppend.computableInPolyTime
    firstTokens secondTokens
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    appended fun source =>
      (UnaryFieldEncoderMachine.unaryFields_append
        (first source) (second source)).symm

private noncomputable def combinedKeysComputableInPolyTime
    {Source InputSymbol : Type}
    [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeSource : Source → List InputSymbol)
    (queries candidateKeys : Source → List Nat)
    (queryCompiler : TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields queries)
    (candidateKeyCompiler : TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields candidateKeys) :
    TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields
      (fun source => combinedKeys (queries source) (candidateKeys source)) := by
  unfold combinedKeys
  exact appendUnaryComputableInPolyTime encodeSource queries candidateKeys
    queryCompiler candidateKeyCompiler

private noncomputable def valueCodesComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (valueCodes (Value := Value)) :=
  FiniteUnaryFieldMap.computableInPolyTime (valueCode (Value := Value))

private noncomputable def metadataComputableInPolyTime
    {Source InputSymbol : Type}
    [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeSource : Source → List InputSymbol)
    (queries : Source → List Nat)
    (candidateValues : Source → List Value)
    (queryCompiler : TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields queries)
    (candidateValueCompiler : TM2ComputableInPolyTime encodeSource id
      candidateValues) :
    TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields
      (fun source => metadata (queries source) (candidateValues source)) := by
  let zeroCompiler := TM2CompositionMachine.computableInPolyTime
    queryCompiler UnaryFieldConstantStreams.zerosComputableInPolyTime
  let codeCompiler := TM2CompositionMachine.computableInPolyTime
    candidateValueCompiler
    (valueCodesComputableInPolyTime (Value := Value))
  unfold metadata
  exact appendUnaryComputableInPolyTime encodeSource
    (fun source => UnaryFieldConstantStreams.zeros (queries source))
    (fun source => valueCodes (candidateValues source))
    zeroCompiler codeCompiler

private noncomputable def keyWordsComputableInPolyTime
    {Source InputSymbol : Type}
    [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeSource : Source → List InputSymbol)
    (queries candidateKeys : Source → List Nat)
    (queryCompiler : TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields queries)
    (candidateKeyCompiler : TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields candidateKeys) :
    TM2ComputableInPolyTime encodeSource
      DelimitedBinaryWords.finEncoding.encode
      (fun source => keyWords (queries source) (candidateKeys source)) := by
  unfold keyWords
  exact TM2CompositionMachine.computableInPolyTime
    (combinedKeysComputableInPolyTime encodeSource queries candidateKeys
      queryCompiler candidateKeyCompiler)
    UnaryFieldBinaryWords.wordsComputableInPolyTime

private noncomputable def metadataWordsComputableInPolyTime
    {Source InputSymbol : Type}
    [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeSource : Source → List InputSymbol)
    (queries : Source → List Nat)
    (candidateValues : Source → List Value)
    (queryCompiler : TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields queries)
    (candidateValueCompiler : TM2ComputableInPolyTime encodeSource id
      candidateValues) :
    TM2ComputableInPolyTime encodeSource
      DelimitedBinaryWords.finEncoding.encode
      (fun source => metadataWords
        (queries source) (candidateValues source)) := by
  unfold metadataWords
  exact TM2CompositionMachine.computableInPolyTime
    (metadataComputableInPolyTime encodeSource queries candidateValues
      queryCompiler candidateValueCompiler)
    UnaryFieldBinaryWords.wordsComputableInPolyTime

private noncomputable def metadataPairsComputableInPolyTime
    {Source InputSymbol : Type}
    [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeSource : Source → List InputSymbol)
    (queries : Source → List Nat)
    (candidateValues : Source → List Value)
    (queryCompiler : TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields queries)
    (candidateValueCompiler : TM2ComputableInPolyTime encodeSource id
      candidateValues) :
    TM2ComputableInPolyTime encodeSource
      DelimitedBinaryWordPairs.finEncoding.encode
      (fun source => metadataPairs
        (queries source) (candidateValues source)) := by
  unfold metadataPairs
  exact TM2CompositionMachine.computableInPolyTime
    (metadataWordsComputableInPolyTime encodeSource queries candidateValues
      queryCompiler candidateValueCompiler)
    DelimitedBinaryWordPairProductMachine.computableInPolyTime

private noncomputable def roleBitsComputableInPolyTime
    {Source InputSymbol : Type}
    [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeSource : Source → List InputSymbol)
    (queries : Source → List Nat)
    (candidateValues : Source → List Value)
    (queryCompiler : TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields queries)
    (candidateValueCompiler : TM2ComputableInPolyTime encodeSource id
      candidateValues) :
    TM2ComputableInPolyTime encodeSource id
      (fun source => roleBits (queries source) (candidateValues source)) := by
  let pairCompiler := metadataPairsComputableInPolyTime encodeSource
    queries candidateValues queryCompiler candidateValueCompiler
  let firstCompiler := TM2CompositionMachine.computableInPolyTime
    pairCompiler (UnaryFieldPairPresence.bitsComputableInPolyTime .first)
  let secondCompiler := TM2CompositionMachine.computableInPolyTime
    pairCompiler (UnaryFieldPairPresence.bitsComputableInPolyTime .second)
  let notFirstCompiler :=
    AlignedBooleanListClosure.mapNegatedComputableInPolyTime
      encodeSource
      (fun source => UnaryFieldPairPresence.bits .first
        (metadataPairs (queries source) (candidateValues source)))
      firstCompiler
  unfold roleBits
  exact AlignedBooleanListClosure.combinedComputableInPolyTime
    encodeSource .conjunction
    (fun source => AlignedBooleanListClosure.negated
      (UnaryFieldPairPresence.bits .first
        (metadataPairs (queries source) (candidateValues source))))
    (fun source => UnaryFieldPairPresence.bits .second
      (metadataPairs (queries source) (candidateValues source)))
    (fun source => by
      simp [AlignedBooleanListClosure.negated,
        UnaryFieldPairPresence.bits])
    notFirstCompiler secondCompiler

private noncomputable def controlsComputableInPolyTime
    {Source InputSymbol : Type}
    [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeSource : Source → List InputSymbol)
    (queries candidateKeys : Source → List Nat)
    (candidateValues : Source → List Value)
    (aligned : ∀ source,
      (candidateKeys source).length = (candidateValues source).length)
    (queryCompiler : TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields queries)
    (candidateKeyCompiler : TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields candidateKeys)
    (candidateValueCompiler : TM2ComputableInPolyTime encodeSource id
      candidateValues) :
    TM2ComputableInPolyTime encodeSource id
      (fun source => controls (queries source) (candidateKeys source)
        (candidateValues source)) := by
  let keyCompiler := keyWordsComputableInPolyTime encodeSource
    queries candidateKeys queryCompiler candidateKeyCompiler
  let equalityCompiler :=
    DelimitedBinaryWordEqualitySquare.equalityBitsComputableInPolyTime
      encodeSource
      (fun source => keyWords (queries source) (candidateKeys source))
      keyCompiler
  let roleCompiler := roleBitsComputableInPolyTime encodeSource
    queries candidateValues queryCompiler candidateValueCompiler
  unfold controls
  exact AlignedBooleanListClosure.combinedComputableInPolyTime
    encodeSource .conjunction
    (fun source => DelimitedBinaryWordEqualitySquare.equalityBits
      (keyWords (queries source) (candidateKeys source)))
    (fun source => roleBits (queries source) (candidateValues source))
    (fun source => by
      rw [DelimitedBinaryWordEqualitySquare.equalityBits_length,
        roleBits_length]
      simp only [keyWords, combinedKeys, UnaryFieldBinaryWords.words,
        List.length_map, List.length_append]
      rw [aligned source])
    equalityCompiler roleCompiler

private noncomputable def repeatedCodesComputableInPolyTime
    {Source InputSymbol : Type}
    [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeSource : Source → List InputSymbol)
    (queries : Source → List Nat)
    (candidateValues : Source → List Value)
    (queryCompiler : TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields queries)
    (candidateValueCompiler : TM2ComputableInPolyTime encodeSource id
      candidateValues) :
    TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields
      (fun source => repeatedCodes
        (queries source) (candidateValues source)) := by
  let pairCompiler := metadataPairsComputableInPolyTime encodeSource
    queries candidateValues queryCompiler candidateValueCompiler
  let complete := TM2CompositionMachine.computableInPolyTime
    pairCompiler DelimitedBinaryWordPairSecondWords.lengthsComputableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq complete
    (fun source => by
      apply congrArg UnaryFieldEncoderMachine.unaryFields
      simp [DelimitedBinaryWordPairSecondWords.lengths,
        DelimitedBinaryWordPairSecondWords.words,
        DelimitedBinaryWordLengths.values, repeatedCodes,
        Function.comp_def])

private theorem selected_lengths_words
    (controls : List Bool) (codes : List Nat) :
    DelimitedBinaryWordLengths.values
        (DelimitedBinaryWordBooleanFilter.selectedWords controls
          (UnaryFieldBinaryWords.words codes)) =
      DelimitedBinaryWordBooleanFilter.selected controls codes := by
  unfold DelimitedBinaryWordLengths.values
    DelimitedBinaryWordBooleanFilter.selectedWords
    UnaryFieldBinaryWords.words
  induction controls generalizing codes with
  | nil => rfl
  | cons active controls induction =>
      cases codes with
      | nil => rfl
      | cons code codes =>
          cases active <;>
            simp [DelimitedBinaryWordBooleanFilter.selected,
              UnaryFieldBinaryWords.word, induction]

private noncomputable def selectedCodesComputableInPolyTime
    {Source InputSymbol : Type}
    [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeSource : Source → List InputSymbol)
    (queries candidateKeys : Source → List Nat)
    (candidateValues : Source → List Value)
    (aligned : ∀ source,
      (candidateKeys source).length = (candidateValues source).length)
    (queryCompiler : TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields queries)
    (candidateKeyCompiler : TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields candidateKeys)
    (candidateValueCompiler : TM2ComputableInPolyTime encodeSource id
      candidateValues) :
    TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields
      (fun source => selectedCodes (queries source) (candidateKeys source)
        (candidateValues source)) := by
  let controlCompiler := controlsComputableInPolyTime encodeSource
    queries candidateKeys candidateValues aligned queryCompiler
    candidateKeyCompiler candidateValueCompiler
  let codeCompiler := repeatedCodesComputableInPolyTime encodeSource
    queries candidateValues queryCompiler candidateValueCompiler
  let wordCompiler := TM2CompositionMachine.computableInPolyTime
    codeCompiler UnaryFieldBinaryWords.wordsComputableInPolyTime
  let filtered :=
    DelimitedBinaryWordBooleanFilter.selectedWordsComputableInPolyTime
      encodeSource
      (fun source => controls (queries source) (candidateKeys source)
        (candidateValues source))
      (fun source => UnaryFieldBinaryWords.words
        (repeatedCodes (queries source) (candidateValues source)))
      controlCompiler wordCompiler
  let measured := TM2CompositionMachine.computableInPolyTime filtered
    DelimitedBinaryWordLengths.valuesComputableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq measured
    (fun source => congrArg UnaryFieldEncoderMachine.unaryFields
      (selected_lengths_words
        (controls (queries source) (candidateKeys source)
          (candidateValues source))
        (repeatedCodes (queries source) (candidateValues source))))

private noncomputable def decodedPairsComputableInPolyTime
    {Source InputSymbol : Type}
    [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeSource : Source → List InputSymbol)
    (queries candidateKeys : Source → List Nat)
    (candidateValues : Source → List Value)
    (aligned : ∀ source,
      (candidateKeys source).length = (candidateValues source).length)
    (queryCompiler : TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields queries)
    (candidateKeyCompiler : TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields candidateKeys)
    (candidateValueCompiler : TM2ComputableInPolyTime encodeSource id
      candidateValues) :
    TM2ComputableInPolyTime encodeSource id
      (fun source => decodedPairs (queries source) (candidateKeys source)
        (candidateValues source)) := by
  let selectedCompiler := selectedCodesComputableInPolyTime encodeSource
    queries candidateKeys candidateValues aligned queryCompiler
    candidateKeyCompiler candidateValueCompiler
  exact TM2CompositionMachine.computableInPolyTime selectedCompiler
    (FiniteIndexSlotUnaryDecoder.computableInPolyTime
      (Fintype.card Value))

/-- Repeated numeric queries can select arbitrary aligned finite-alphabet
candidate values in polynomial time.  Duplicate candidate keys deliberately
emit every matching value in candidate order. -/
noncomputable def valuesComputableInPolyTime
    {Source InputSymbol : Type}
    [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeSource : Source → List InputSymbol)
    (queries candidateKeys : Source → List Nat)
    (candidateValues : Source → List Value)
    (aligned : ∀ source,
      (candidateKeys source).length = (candidateValues source).length)
    (queryCompiler : TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields queries)
    (candidateKeyCompiler : TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields candidateKeys)
    (candidateValueCompiler : TM2ComputableInPolyTime encodeSource id
      candidateValues) :
    TM2ComputableInPolyTime encodeSource id
      (fun source => values (queries source) (candidateKeys source)
        (candidateValues source)) := by
  letI : Inhabited Value :=
    ⟨Classical.choice (inferInstance : Nonempty Value)⟩
  let pairCompiler := decodedPairsComputableInPolyTime encodeSource
    queries candidateKeys candidateValues aligned queryCompiler
    candidateKeyCompiler candidateValueCompiler
  let mapped := FiniteBlockTransducer.computableInPolyTime
    (fun pair : DecodedPair Value => [pairValue pair])
  let complete := TM2CompositionMachine.computableInPolyTime
    pairCompiler mapped
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq complete
    fun source => by
      unfold values
      rw [← List.map_eq_flatMap]

end LeanTrominoes.FiniteAlphabetKeyedValueLookup

end
