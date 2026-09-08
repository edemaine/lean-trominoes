/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordBooleanFilterCompiler
import LeanTrominoes.DelimitedBinaryWordEqualitySquareCompiler
import LeanTrominoes.DelimitedBinaryWordEqualitySquareSemantics
import LeanTrominoes.DelimitedBinaryWordLengthsCompiler
import LeanTrominoes.DelimitedBinaryWordsAppendClosure
import LeanTrominoes.LastTrueUnaryValueLookupTime
import LeanTrominoes.LastTrueUnaryValueLookupValidity
import LeanTrominoes.UnaryFieldConstantBitCompiler
import LeanTrominoes.UnaryFieldConstantStreamCompiler
import LeanTrominoes.UnaryFieldEncoderAppendClosure

/-! # Aligned unary-value lookup by binary-word keys -/

noncomputable section

namespace LeanTrominoes.DelimitedBinaryWordKeyedValueLookup

open Computability Turing

local instance : Inhabited DelimitedBinaryWords.finEncoding.Γ := ⟨.wordStart⟩

/-- Keep exactly the equality rows corresponding to queries. -/
def rowControls (queries candidates : DelimitedBinaryWords.Input) : List Bool :=
  queries.words.map (fun _ => true) ++ candidates.words.map (fun _ => false)

def queryRows (queries candidates : DelimitedBinaryWords.Input) : DelimitedBinaryWords.Input :=
  DelimitedBinaryWordBooleanFilter.selectedWords (rowControls queries candidates)
    (DelimitedBinaryWordEqualitySquare.rows (DelimitedBinaryWords.append queries candidates))

/-- The query prefix has zero values, so a missing candidate key returns zero. -/
def paddedValues (queries : DelimitedBinaryWords.Input) (candidateValues : List Nat) : List Nat :=
  List.replicate queries.words.length 0 ++ candidateValues

/-- Repeated queries select their last equal candidate, preserving query order. -/
def values (queries candidates : DelimitedBinaryWords.Input)
    (candidateValues : List Nat) : List Nat :=
  LastTrueUnaryValueLookupMachine.lookups (queryRows queries candidates).words
    (paddedValues queries candidateValues)

private theorem rows_valid (queries candidates : DelimitedBinaryWords.Input)
    (candidateValues : List Nat) (aligned : candidateValues.length = candidates.words.length) :
    (queryRows queries candidates).words.Forall fun row =>
      row.length = (paddedValues queries candidateValues).length := by
  unfold queryRows DelimitedBinaryWordBooleanFilter.selectedWords
  apply DelimitedBinaryWordBooleanFilter.selected_forall
  rw [DelimitedBinaryWordEqualitySquare.rows_words]
  unfold LastRepresentativeEqualityRows.equalityRows
  rw [List.forall_iff_forall_mem]
  intro row member
  obtain ⟨word, _member, rfl⟩ := List.mem_map.mp member
  simp [LastRepresentativeEqualityRows.equalityRow, paddedValues, aligned]

private def input (queries candidates : DelimitedBinaryWords.Input)
    (candidateValues : List Nat) (aligned : candidateValues.length = candidates.words.length) :
    LastTrueUnaryValueLookupMachine.Input where
  rows := (queryRows queries candidates).words
  values := paddedValues queries candidateValues
  valid := LastTrueUnaryValueLookupMachine.RowsValid.of_forall_length
    (rows_valid queries candidates candidateValues aligned)

/-- Lookup uses literal word equality, so even long binary keys need no
conversion to exponentially large unary integers. -/
noncomputable def valuesComputableInPolyTime
    {InputSymbol : Type} [Fintype InputSymbol] [Inhabited InputSymbol]
    (queries candidates : List InputSymbol → DelimitedBinaryWords.Input)
    (candidateValues : List InputSymbol → List Nat)
    (aligned : ∀ source, (candidateValues source).length = (candidates source).words.length)
    (queryCompiler : TM2ComputableInPolyTime id DelimitedBinaryWords.finEncoding.encode queries)
    (candidateCompiler :
      TM2ComputableInPolyTime id DelimitedBinaryWords.finEncoding.encode candidates)
    (valueCompiler :
      TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields candidateValues) :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun source => values (queries source) (candidates source) (candidateValues source)) := by
  let queryLengths := TM2CompositionMachine.computableInPolyTime
    queryCompiler DelimitedBinaryWordLengths.valuesComputableInPolyTime
  let candidateLengths := TM2CompositionMachine.computableInPolyTime
    candidateCompiler DelimitedBinaryWordLengths.valuesComputableInPolyTime
  let queryBits := TM2CompositionMachine.computableInPolyTime
    queryLengths (UnaryFieldConstantBits.computableInPolyTime true)
  let candidateBits := TM2CompositionMachine.computableInPolyTime
    candidateLengths (UnaryFieldConstantBits.computableInPolyTime false)
  have controls : TM2ComputableInPolyTime id id
      (fun source => rowControls (queries source) (candidates source)) := by
    simpa [rowControls, UnaryFieldConstantBits.values,
      DelimitedBinaryWordLengths.values, List.map_map] using
      TM2ListAppend.computableInPolyTime queryBits candidateBits
  let combined := DelimitedBinaryWords.appendComputableInPolyTime queryCompiler candidateCompiler
  let rows := DelimitedBinaryWordEqualitySquare.rowsComputableInPolyTime id
    (fun source => DelimitedBinaryWords.append (queries source) (candidates source)) combined
  let selected := DelimitedBinaryWordBooleanFilter.selectedWordsComputableInPolyTime id
    (fun source => rowControls (queries source) (candidates source))
    (fun source => DelimitedBinaryWordEqualitySquare.rows
      (DelimitedBinaryWords.append (queries source) (candidates source))) controls rows
  let zeros := TM2CompositionMachine.computableInPolyTime
    queryLengths UnaryFieldConstantStreams.zerosComputableInPolyTime
  have padded : TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (fun source => paddedValues (queries source) (candidateValues source)) := by
    simpa [paddedValues, UnaryFieldConstantStreams.zeros,
      DelimitedBinaryWordLengths.values, List.map_map, Function.comp_def] using
      UnaryFieldEncoderMachine.appendComputableInPolyTime zeros valueCompiler
  let forked := TM2ForkMachine.computableInPolyTime selected padded
  have prepared : TM2ComputableInPolyTime id LastTrueUnaryValueLookupMachine.encode
      (fun source => input (queries source) (candidates source)
        (candidateValues source) (aligned source)) :=
    TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq forked (fun _ => rfl)
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (TM2CompositionMachine.computableInPolyTime prepared
      LastTrueUnaryValueLookupMachine.computableInPolyTime) (fun _ => rfl)

end LeanTrominoes.DelimitedBinaryWordKeyedValueLookup

end
