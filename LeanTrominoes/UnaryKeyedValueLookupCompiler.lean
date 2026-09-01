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

/-! # Unary value lookup by repeated numeric keys -/

noncomputable section

namespace LeanTrominoes.UnaryKeyedValueLookup

open Computability Turing

local instance : Inhabited DelimitedBinaryWords.finEncoding.Γ :=
  ⟨DelimitedBinaryWords.Token.wordStart⟩

/-- Query keys precede the aligned candidate keys. -/
def combinedKeys (queries candidateKeys : List Nat) : List Nat :=
  queries ++ candidateKeys

/-- Select precisely the equality rows belonging to the query prefix. -/
def rowControls (queries candidateKeys : List Nat) : List Bool :=
  queries.map (fun _ => true) ++ candidateKeys.map (fun _ => false)

def allRows (queries candidateKeys : List Nat) :
    DelimitedBinaryWords.Input :=
  DelimitedBinaryWordEqualitySquare.rows
    (UnaryFieldBinaryWords.words (combinedKeys queries candidateKeys))

def queryRows (queries candidateKeys : List Nat) :
    DelimitedBinaryWords.Input :=
  DelimitedBinaryWordBooleanFilter.selectedWords
    (rowControls queries candidateKeys)
    (allRows queries candidateKeys)

/-- Query columns carry harmless zeros; candidate columns carry their aligned
values.  A present query key therefore selects its last candidate value. -/
def paddedValues (queries candidateValues : List Nat) : List Nat :=
  UnaryFieldConstantStreams.zeros queries ++ candidateValues

theorem allRows_forall_combinedLength
    (queries candidateKeys : List Nat) :
    (allRows queries candidateKeys).words.Forall fun row =>
      row.length = (combinedKeys queries candidateKeys).length := by
  unfold allRows
  rw [DelimitedBinaryWordEqualitySquare.rows_words]
  unfold LastRepresentativeEqualityRows.equalityRows
  rw [List.forall_iff_forall_mem]
  intro row rowMember
  obtain ⟨word, _wordMember, rfl⟩ := List.mem_map.mp rowMember
  simp [LastRepresentativeEqualityRows.equalityRow,
    UnaryFieldBinaryWords.words]

@[simp] theorem paddedValues_length
    (queries candidateKeys candidateValues : List Nat)
    (aligned : candidateValues.length = candidateKeys.length) :
    (paddedValues queries candidateValues).length =
      (combinedKeys queries candidateKeys).length := by
  simp [paddedValues, combinedKeys, UnaryFieldConstantStreams.zeros,
    aligned]

theorem queryRows_forall_paddedValuesLength
    (queries candidateKeys candidateValues : List Nat)
    (aligned : candidateValues.length = candidateKeys.length) :
    (queryRows queries candidateKeys).words.Forall fun row =>
      row.length = (paddedValues queries candidateValues).length := by
  unfold queryRows DelimitedBinaryWordBooleanFilter.selectedWords
  exact DelimitedBinaryWordBooleanFilter.selected_forall
    (fun row : List Bool =>
      row.length = (paddedValues queries candidateValues).length)
    (rowControls queries candidateKeys)
    (allRows queries candidateKeys).words
    ((allRows_forall_combinedLength queries candidateKeys).imp
      (fun _row rowLength => rowLength.trans
        (paddedValues_length queries candidateKeys candidateValues
          aligned).symm))

def input (queries candidateKeys candidateValues : List Nat)
    (aligned : candidateValues.length = candidateKeys.length) :
    LastTrueUnaryValueLookupMachine.Input where
  rows := (queryRows queries candidateKeys).words
  values := paddedValues queries candidateValues
  valid := LastTrueUnaryValueLookupMachine.RowsValid.of_forall_length
    (queryRows_forall_paddedValuesLength queries candidateKeys
      candidateValues aligned)

/-- Values selected by repeated numeric keys.  A missing key retains the
lookup machine's total zero fallback. -/
def values (queries candidateKeys candidateValues : List Nat) : List Nat :=
  LastTrueUnaryValueLookupMachine.lookups
    (queryRows queries candidateKeys).words
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
      (fun source => combinedKeys
        (queries source) (candidateKeys source)) := by
  unfold combinedKeys
  exact appendUnaryComputableInPolyTime encodeSource queries candidateKeys
    queryCompiler candidateKeyCompiler

private noncomputable def rowControlsComputableInPolyTime
    {Source InputSymbol : Type}
    [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeSource : Source → List InputSymbol)
    (queries candidateKeys : Source → List Nat)
    (queryCompiler : TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields queries)
    (candidateKeyCompiler : TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields candidateKeys) :
    TM2ComputableInPolyTime encodeSource id
      (fun source => rowControls
        (queries source) (candidateKeys source)) := by
  let queryBits := TM2CompositionMachine.computableInPolyTime
    queryCompiler (UnaryFieldConstantBits.computableInPolyTime true)
  let candidateBits := TM2CompositionMachine.computableInPolyTime
    candidateKeyCompiler (UnaryFieldConstantBits.computableInPolyTime false)
  simpa [rowControls, UnaryFieldConstantBits.values] using
    (TM2ListAppend.computableInPolyTime queryBits candidateBits)

private noncomputable def allRowsComputableInPolyTime
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
      (fun source => allRows
        (queries source) (candidateKeys source)) := by
  let keysCompiler := combinedKeysComputableInPolyTime encodeSource
    queries candidateKeys queryCompiler candidateKeyCompiler
  let wordCompiler := TM2CompositionMachine.computableInPolyTime
    keysCompiler UnaryFieldBinaryWords.wordsComputableInPolyTime
  exact DelimitedBinaryWordEqualitySquare.rowsComputableInPolyTime
    encodeSource
    (fun source => UnaryFieldBinaryWords.words
      (combinedKeys (queries source) (candidateKeys source)))
    wordCompiler

private noncomputable def queryRowsComputableInPolyTime
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
      (fun source => queryRows
        (queries source) (candidateKeys source)) := by
  exact DelimitedBinaryWordBooleanFilter.selectedWordsComputableInPolyTime
    encodeSource
    (fun source => rowControls (queries source) (candidateKeys source))
    (fun source => allRows (queries source) (candidateKeys source))
    (rowControlsComputableInPolyTime encodeSource queries candidateKeys
      queryCompiler candidateKeyCompiler)
    (allRowsComputableInPolyTime encodeSource queries candidateKeys
      queryCompiler candidateKeyCompiler)

private noncomputable def paddedValuesComputableInPolyTime
    {Source InputSymbol : Type}
    [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeSource : Source → List InputSymbol)
    (queries candidateValues : Source → List Nat)
    (queryCompiler : TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields queries)
    (candidateValueCompiler : TM2ComputableInPolyTime encodeSource
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
    candidateValues zeroCompiler candidateValueCompiler

/-- Repeated query keys can select values from any aligned compiled
key/value columns in polynomial time. -/
noncomputable def valuesComputableInPolyTime
    {Source InputSymbol : Type}
    [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeSource : Source → List InputSymbol)
    (queries candidateKeys candidateValues : Source → List Nat)
    (aligned : ∀ source,
      (candidateValues source).length = (candidateKeys source).length)
    (queryCompiler : TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields queries)
    (candidateKeyCompiler : TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields candidateKeys)
    (candidateValueCompiler : TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields candidateValues) :
    TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields
      (fun source => values (queries source) (candidateKeys source)
        (candidateValues source)) := by
  let rowCompiler := queryRowsComputableInPolyTime encodeSource
    queries candidateKeys queryCompiler candidateKeyCompiler
  let valueCompiler := paddedValuesComputableInPolyTime encodeSource
    queries candidateValues queryCompiler candidateValueCompiler
  let forked := TM2ForkMachine.computableInPolyTime
    rowCompiler valueCompiler
  let prepared : TM2ComputableInPolyTime encodeSource
      LastTrueUnaryValueLookupMachine.encode
      (fun source => input (queries source) (candidateKeys source)
        (candidateValues source) (aligned source)) :=
    TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
      forked (fun _ => rfl)
  let lookedUp := TM2CompositionMachine.computableInPolyTime prepared
    LastTrueUnaryValueLookupMachine.computableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    lookedUp (fun _ => rfl)

end LeanTrominoes.UnaryKeyedValueLookup

end
