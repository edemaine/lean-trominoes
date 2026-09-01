/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordBooleanFilterCompiler
import LeanTrominoes.DelimitedBinaryWordEqualitySquareCompiler
import LeanTrominoes.DelimitedBinaryWordEqualitySquareSemantics
import LeanTrominoes.LastTrueUnaryValueLookupTime
import LeanTrominoes.LastTrueUnaryValueLookupValidity
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2ForkMachineTime
import LeanTrominoes.TM2ListAppendClosure
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport
import LeanTrominoes.UnaryFieldBinaryWordCompiler
import LeanTrominoes.UnaryFieldConstantBitCompiler
import LeanTrominoes.UnaryFieldConstantStreamCompiler
import LeanTrominoes.UnaryFieldEncoderFlatMapSemantics
import LeanTrominoes.UnaryFieldRangeCompiler

/-! # Unary value lookup by repeated numeric indices -/

noncomputable section

namespace LeanTrominoes.UnaryIndexedValueLookup

open Computability Turing

local instance : Inhabited DelimitedBinaryWords.finEncoding.Γ :=
  ⟨DelimitedBinaryWords.Token.wordStart⟩

/-- Canonical zero-based keys of the candidate value column. -/
def candidateKeys (candidateValues : List Nat) : List Nat :=
  List.range candidateValues.length

/-- Query keys precede the unique candidate keys. -/
def combinedKeys (queries candidateValues : List Nat) : List Nat :=
  queries ++ candidateKeys candidateValues

/-- Select precisely the equality rows belonging to the query prefix. -/
def rowControls (queries candidateValues : List Nat) : List Bool :=
  queries.map (fun _ => true) ++ candidateValues.map (fun _ => false)

def allRows (queries candidateValues : List Nat) :
    DelimitedBinaryWords.Input :=
  DelimitedBinaryWordEqualitySquare.rows
    (UnaryFieldBinaryWords.words (combinedKeys queries candidateValues))

def queryRows (queries candidateValues : List Nat) :
    DelimitedBinaryWords.Input :=
  DelimitedBinaryWordBooleanFilter.selectedWords
    (rowControls queries candidateValues)
    (allRows queries candidateValues)

/-- Query columns carry harmless zeros; candidate columns carry the values
being indexed.  Every valid query has a later matching candidate column, so
last-true lookup selects that candidate rather than an earlier query. -/
def paddedValues (queries candidateValues : List Nat) : List Nat :=
  UnaryFieldConstantStreams.zeros queries ++ candidateValues

theorem allRows_forall_combinedLength
    (queries candidateValues : List Nat) :
    (allRows queries candidateValues).words.Forall fun row =>
      row.length = (combinedKeys queries candidateValues).length := by
  unfold allRows
  rw [DelimitedBinaryWordEqualitySquare.rows_words]
  unfold LastRepresentativeEqualityRows.equalityRows
  rw [List.forall_iff_forall_mem]
  intro row rowMember
  obtain ⟨word, _wordMember, rfl⟩ := List.mem_map.mp rowMember
  simp [LastRepresentativeEqualityRows.equalityRow,
    UnaryFieldBinaryWords.words]

@[simp] theorem paddedValues_length
    (queries candidateValues : List Nat) :
    (paddedValues queries candidateValues).length =
      (combinedKeys queries candidateValues).length := by
  simp [paddedValues, combinedKeys, candidateKeys,
    UnaryFieldConstantStreams.zeros]

theorem queryRows_forall_paddedValuesLength
    (queries candidateValues : List Nat) :
    (queryRows queries candidateValues).words.Forall fun row =>
      row.length = (paddedValues queries candidateValues).length := by
  unfold queryRows DelimitedBinaryWordBooleanFilter.selectedWords
  exact DelimitedBinaryWordBooleanFilter.selected_forall
    (fun row : List Bool =>
      row.length = (paddedValues queries candidateValues).length)
    (rowControls queries candidateValues)
    (allRows queries candidateValues).words
    ((allRows_forall_combinedLength queries candidateValues).imp
      (fun _row rowLength => rowLength.trans
        (paddedValues_length queries candidateValues).symm))

def input (queries candidateValues : List Nat) :
    LastTrueUnaryValueLookupMachine.Input where
  rows := (queryRows queries candidateValues).words
  values := paddedValues queries candidateValues
  valid := LastTrueUnaryValueLookupMachine.RowsValid.of_forall_length
    (queryRows_forall_paddedValuesLength queries candidateValues)

/-- Values selected by every possibly repeated zero-based query.  Out-of-range
queries retain the lookup machine's total fallback behavior. -/
def values (queries candidateValues : List Nat) : List Nat :=
  LastTrueUnaryValueLookupMachine.lookups
    (queryRows queries candidateValues).words
    (paddedValues queries candidateValues)

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

private noncomputable def candidateKeysComputableInPolyTime
    {Source InputSymbol : Type}
    [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeSource : Source → List InputSymbol)
    (candidateValues : Source → List Nat)
    (candidateCompiler : TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields candidateValues) :
    TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields
      (fun source => candidateKeys (candidateValues source)) := by
  let ranged := TM2CompositionMachine.computableInPolyTime
    candidateCompiler UnaryFieldRange.computableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    ranged fun source => congrArg UnaryFieldEncoderMachine.unaryFields (by
      simp [UnaryFieldRange.values, candidateKeys])

private noncomputable def combinedKeysComputableInPolyTime
    {Source InputSymbol : Type}
    [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeSource : Source → List InputSymbol)
    (queries candidateValues : Source → List Nat)
    (queryCompiler : TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields queries)
    (candidateCompiler : TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields candidateValues) :
    TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields
      (fun source => combinedKeys
        (queries source) (candidateValues source)) := by
  unfold combinedKeys
  exact appendUnaryComputableInPolyTime encodeSource queries
    (fun source => candidateKeys (candidateValues source))
    queryCompiler
    (candidateKeysComputableInPolyTime encodeSource candidateValues
      candidateCompiler)

private noncomputable def rowControlsComputableInPolyTime
    {Source InputSymbol : Type}
    [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeSource : Source → List InputSymbol)
    (queries candidateValues : Source → List Nat)
    (queryCompiler : TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields queries)
    (candidateCompiler : TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields candidateValues) :
    TM2ComputableInPolyTime encodeSource id
      (fun source => rowControls
        (queries source) (candidateValues source)) := by
  let queryBits := TM2CompositionMachine.computableInPolyTime
    queryCompiler (UnaryFieldConstantBits.computableInPolyTime true)
  let candidateBits := TM2CompositionMachine.computableInPolyTime
    candidateCompiler (UnaryFieldConstantBits.computableInPolyTime false)
  simpa [rowControls, UnaryFieldConstantBits.values] using
    (TM2ListAppend.computableInPolyTime queryBits candidateBits)

private noncomputable def allRowsComputableInPolyTime
    {Source InputSymbol : Type}
    [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeSource : Source → List InputSymbol)
    (queries candidateValues : Source → List Nat)
    (queryCompiler : TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields queries)
    (candidateCompiler : TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields candidateValues) :
    TM2ComputableInPolyTime encodeSource
      DelimitedBinaryWords.finEncoding.encode
      (fun source => allRows
        (queries source) (candidateValues source)) := by
  let keysCompiler := combinedKeysComputableInPolyTime encodeSource
    queries candidateValues queryCompiler candidateCompiler
  let wordCompiler := TM2CompositionMachine.computableInPolyTime
    keysCompiler UnaryFieldBinaryWords.wordsComputableInPolyTime
  exact DelimitedBinaryWordEqualitySquare.rowsComputableInPolyTime
    encodeSource
    (fun source => UnaryFieldBinaryWords.words
      (combinedKeys (queries source) (candidateValues source)))
    wordCompiler

private noncomputable def queryRowsComputableInPolyTime
    {Source InputSymbol : Type}
    [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeSource : Source → List InputSymbol)
    (queries candidateValues : Source → List Nat)
    (queryCompiler : TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields queries)
    (candidateCompiler : TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields candidateValues) :
    TM2ComputableInPolyTime encodeSource
      DelimitedBinaryWords.finEncoding.encode
      (fun source => queryRows
        (queries source) (candidateValues source)) := by
  exact DelimitedBinaryWordBooleanFilter.selectedWordsComputableInPolyTime
    encodeSource
    (fun source => rowControls (queries source) (candidateValues source))
    (fun source => allRows (queries source) (candidateValues source))
    (rowControlsComputableInPolyTime encodeSource queries candidateValues
      queryCompiler candidateCompiler)
    (allRowsComputableInPolyTime encodeSource queries candidateValues
      queryCompiler candidateCompiler)

private noncomputable def paddedValuesComputableInPolyTime
    {Source InputSymbol : Type}
    [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeSource : Source → List InputSymbol)
    (queries candidateValues : Source → List Nat)
    (queryCompiler : TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields queries)
    (candidateCompiler : TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields candidateValues) :
    TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields
      (fun source => paddedValues
        (queries source) (candidateValues source)) := by
  let zeroCompiler := TM2CompositionMachine.computableInPolyTime
    queryCompiler UnaryFieldConstantStreams.zerosComputableInPolyTime
  unfold paddedValues
  exact appendUnaryComputableInPolyTime encodeSource
    (fun source => UnaryFieldConstantStreams.zeros (queries source))
    candidateValues zeroCompiler candidateCompiler

/-- Repeated arbitrary query indices can select a compiled unary candidate
column in polynomial time. -/
noncomputable def valuesComputableInPolyTime
    {Source InputSymbol : Type}
    [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeSource : Source → List InputSymbol)
    (queries candidateValues : Source → List Nat)
    (queryCompiler : TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields queries)
    (candidateCompiler : TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields candidateValues) :
    TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields
      (fun source => values
        (queries source) (candidateValues source)) := by
  let rowCompiler := queryRowsComputableInPolyTime encodeSource
    queries candidateValues queryCompiler candidateCompiler
  let valueCompiler := paddedValuesComputableInPolyTime encodeSource
    queries candidateValues queryCompiler candidateCompiler
  let forked := TM2ForkMachine.computableInPolyTime
    rowCompiler valueCompiler
  let prepared : TM2ComputableInPolyTime encodeSource
      LastTrueUnaryValueLookupMachine.encode
      (fun source => input (queries source) (candidateValues source)) :=
    TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
      forked (fun _ => rfl)
  let lookedUp := TM2CompositionMachine.computableInPolyTime prepared
    LastTrueUnaryValueLookupMachine.computableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    lookedUp (fun _ => rfl)

end LeanTrominoes.UnaryIndexedValueLookup

end
