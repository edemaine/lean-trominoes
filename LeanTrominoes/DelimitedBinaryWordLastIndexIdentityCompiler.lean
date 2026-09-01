/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordEqualitySquareCompiler
import LeanTrominoes.DelimitedBinaryWordEqualitySquareSemantics
import LeanTrominoes.DelimitedBinaryWordTrueCountCompiler
import LeanTrominoes.LastTrueUnaryValueLookupTime
import LeanTrominoes.LastTrueUnaryValueLookupValidity
import LeanTrominoes.TM2ForkMachineTime
import LeanTrominoes.UnaryFieldRangeCompiler

/-! # Canonical last-index identities of delimited binary words -/

noncomputable section

namespace LeanTrominoes.DelimitedBinaryWordLastIndexIdentity

open Computability Turing

def equalityRows (input : DelimitedBinaryWords.Input) :
    DelimitedBinaryWords.Input :=
  DelimitedBinaryWordEqualitySquare.rows input

/-- The natural presentation index attached to every word column. -/
def positionValues (input : DelimitedBinaryWords.Input) : List Nat :=
  List.range input.words.length

theorem equalityRows_forall_positionLength
    (input : DelimitedBinaryWords.Input) :
    (equalityRows input).words.Forall fun row =>
      row.length = (positionValues input).length := by
  unfold equalityRows
  rw [DelimitedBinaryWordEqualitySquare.rows_words,
    List.forall_iff_forall_mem]
  intro row rowMember
  unfold LastRepresentativeEqualityRows.equalityRows at rowMember
  rcases List.mem_map.mp rowMember with ⟨word, _wordMember, rfl⟩
  simp [LastRepresentativeEqualityRows.equalityRow, positionValues]

def lookupInput (input : DelimitedBinaryWords.Input) :
    LastTrueUnaryValueLookupMachine.Input where
  rows := (equalityRows input).words
  values := positionValues input
  valid := LastTrueUnaryValueLookupMachine.RowsValid.of_forall_length
    (equalityRows_forall_positionLength input)

/-- For every word, the final presentation index occupied by an equal word.
This is a canonical numeric identity of the represented word. -/
def identityIndices (input : DelimitedBinaryWords.Input) : List Nat :=
  LastTrueUnaryValueLookupMachine.lookups
    (lookupInput input).rows (lookupInput input).values

@[simp] theorem identityIndices_length
    (input : DelimitedBinaryWords.Input) :
    (identityIndices input).length = input.words.length := by
  unfold identityIndices LastTrueUnaryValueLookupMachine.lookups
  change ((equalityRows input).words.map fun row =>
      LastTrueUnaryValueLookupMachine.lookup row
        (positionValues input)).length = input.words.length
  rw [List.length_map]
  unfold equalityRows
  rw [DelimitedBinaryWordEqualitySquare.rows_words]
  simp [LastRepresentativeEqualityRows.equalityRows]

/-- Canonical word identities are polynomial-time computable after any
polynomial-time delimited-word emitter. -/
noncomputable def computableInPolyTime
    {Source InputSymbol : Type}
    [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeSource : Source → List InputSymbol)
    (words : Source → DelimitedBinaryWords.Input)
    (wordCompiler :
      @TM2ComputableInPolyTime Source DelimitedBinaryWords.Input
        InputSymbol DelimitedBinaryWords.Token encodeSource
        DelimitedBinaryWords.finEncoding.encode words) :
    @TM2ComputableInPolyTime Source (List Nat) InputSymbol
      UnaryFieldEncoderMachine.Symbol encodeSource
      UnaryFieldEncoderMachine.unaryFields
      (fun source => identityIndices (words source)) := by
  let rowCompiler :=
    DelimitedBinaryWordEqualitySquare.rowsComputableInPolyTime
      encodeSource words wordCompiler
  let counted := TM2CompositionMachine.computableInPolyTime
    wordCompiler DelimitedBinaryWordTrueCounts.computableInPolyTime
  let ranged := TM2CompositionMachine.computableInPolyTime
    counted UnaryFieldRange.computableInPolyTime
  let positionCompiler : @TM2ComputableInPolyTime
      Source (List Nat) InputSymbol UnaryFieldEncoderMachine.Symbol
      encodeSource UnaryFieldEncoderMachine.unaryFields
      (fun source => positionValues (words source)) :=
    TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq ranged
      (fun source => by
        apply congrArg UnaryFieldEncoderMachine.unaryFields
        simp [UnaryFieldRange.values, DelimitedBinaryWordTrueCounts.counts,
          positionValues])
  let forked := TM2ForkMachine.computableInPolyTime
    rowCompiler positionCompiler
  let prepared : @TM2ComputableInPolyTime
      Source LastTrueUnaryValueLookupMachine.Input InputSymbol
      LastTrueUnaryValueLookupMachine.InputSymbol encodeSource
      LastTrueUnaryValueLookupMachine.encode
      (fun source => lookupInput (words source)) :=
    TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq forked
      (fun _ => rfl)
  let lookedUp := TM2CompositionMachine.computableInPolyTime prepared
    LastTrueUnaryValueLookupMachine.computableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq lookedUp
    (fun _ => rfl)

end LeanTrominoes.DelimitedBinaryWordLastIndexIdentity

end
