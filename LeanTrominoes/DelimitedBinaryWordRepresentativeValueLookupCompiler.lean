/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordRepresentativeSquareCompiler
import LeanTrominoes.DelimitedBinaryWordRepresentativeSquareSemantics
import LeanTrominoes.LastRepresentativeEqualityRowsSemantics
import LeanTrominoes.LastTrueUnaryValueLookupCompiler
import LeanTrominoes.LastTrueUnaryValueLookupValidity
import LeanTrominoes.TM2ForkMachineTime
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Unary values at last binary-word representatives -/

noncomputable section

namespace LeanTrominoes.DelimitedBinaryWordRepresentativeValueLookup

open Computability Turing

local instance : Inhabited DelimitedBinaryWords.Token :=
  ⟨DelimitedBinaryWords.Token.wordStart⟩

/-- Last-representative equality rows retain the full original column
width. -/
theorem rows_forall_length (words : DelimitedBinaryWords.Input) :
    (DelimitedBinaryWordRepresentativeSquare.rows words).words.Forall
      fun row => row.length = words.words.length := by
  unfold DelimitedBinaryWordRepresentativeSquare.rows
  rw [DelimitedBinaryWordEqualitySquare.rows_eq]
  rw [LastRepresentativeEqualityRows.rows_equalityRows]
  rw [List.forall_iff_forall_mem]
  intro row rowMember
  obtain ⟨word, _wordMember, rfl⟩ := List.mem_map.mp rowMember
  unfold LastRepresentativeEqualityRows.equalityRow
  rw [List.length_map]

def input (words : DelimitedBinaryWords.Input)
    (candidateValues : List Nat)
    (lengthEq : candidateValues.length = words.words.length) :
    LastTrueUnaryValueLookupMachine.Input where
  rows := (DelimitedBinaryWordRepresentativeSquare.rows words).words
  values := candidateValues
  valid := LastTrueUnaryValueLookupMachine.RowsValid.of_forall_length
    ((rows_forall_length words).imp fun _row rowLength =>
      rowLength.trans lengthEq.symm)

/-- Look up an aligned unary datum once at each distinct binary word, in
stable last-occurrence order. -/
def selectedValues (words : DelimitedBinaryWords.Input)
    (candidateValues : List Nat) : List Nat :=
  LastTrueUnaryValueLookupMachine.lookups
    (DelimitedBinaryWordRepresentativeSquare.rows words).words
    candidateValues

/-- Last-representative selection preserves polynomial time for any compiled
word stream and exactly aligned unary value stream. -/
noncomputable def selectedValuesComputableInPolyTime
    {Source InputSymbol : Type}
    [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeSource : Source → List InputSymbol)
    (words : Source → DelimitedBinaryWords.Input)
    (candidateValues : Source → List Nat)
    (lengthEq : ∀ source,
      (candidateValues source).length = (words source).words.length)
    (wordCompiler :
      @TM2ComputableInPolyTime
        Source DelimitedBinaryWords.Input InputSymbol
        DelimitedBinaryWords.Token encodeSource
        DelimitedBinaryWords.finEncoding.encode words)
    (candidateCompiler :
      @TM2ComputableInPolyTime
        Source (List Nat) InputSymbol UnaryFieldEncoderMachine.Symbol
        encodeSource UnaryFieldEncoderMachine.unaryFields candidateValues) :
    @TM2ComputableInPolyTime
      Source (List Nat) InputSymbol UnaryFieldEncoderMachine.Symbol
      encodeSource UnaryFieldEncoderMachine.unaryFields
      (fun source => selectedValues
        (words source) (candidateValues source)) := by
  let rowCompiler :=
    DelimitedBinaryWordRepresentativeSquare.rowsComputableInPolyTime
      encodeSource words wordCompiler
  let paired := TM2ForkMachine.computableInPolyTime
    rowCompiler candidateCompiler
  let prepared : TM2ComputableInPolyTime encodeSource
      LastTrueUnaryValueLookupMachine.encode
      (fun source => input
        (words source) (candidateValues source) (lengthEq source)) :=
    TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq paired
      (fun _ => rfl)
  let lookedUp := LastTrueUnaryValueLookupMachine.afterComputableInPolyTime
    encodeSource
    (fun source => input
      (words source) (candidateValues source) (lengthEq source))
    prepared
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    lookedUp (fun _ => rfl)

end LeanTrominoes.DelimitedBinaryWordRepresentativeValueLookup

end
