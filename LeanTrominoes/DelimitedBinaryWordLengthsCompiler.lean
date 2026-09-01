/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWords
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.TM2PolyTimeInputEncodingTransport
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport
import LeanTrominoes.UnaryFieldEncoderMachine

/-! # Lengths of delimiter-encoded binary words -/

noncomputable section

namespace LeanTrominoes.DelimitedBinaryWordLengths

open Computability Turing

abbrev WordToken := DelimitedBinaryWords.Token
abbrev UnarySymbol := UnaryFieldEncoderMachine.Symbol

/-- The length of every semantic binary word. -/
def values (input : DelimitedBinaryWords.Input) : List Nat :=
  input.words.map List.length

/-- Erase word starts, turn every bit into one unary unit, and turn every word
end into one unary-field delimiter. -/
def tokenBlock : WordToken → List UnarySymbol
  | .wordStart => []
  | .bit _ => [.unit]
  | .wordEnd => [.delimiter]

def tokens (source : List WordToken) : List UnarySymbol :=
  source.flatMap tokenBlock

private theorem flatMap_bit_tokenBlock (word : List Bool) :
    (word.map DelimitedBinaryWords.Token.bit).flatMap tokenBlock =
      List.replicate word.length UnaryFieldEncoderMachine.Symbol.unit := by
  induction word with
  | nil => rfl
  | cons bit word induction =>
      simp [tokenBlock, List.replicate_succ, induction]

@[simp] theorem tokens_wordTokens (word : List Bool) :
    tokens (DelimitedBinaryWords.wordTokens word) =
      UnaryFieldEncoderMachine.unaryField word.length := by
  simp [tokens, tokenBlock, DelimitedBinaryWords.wordTokens,
    UnaryFieldEncoderMachine.unaryField, flatMap_bit_tokenBlock]

@[simp] theorem tokens_encode (input : DelimitedBinaryWords.Input) :
    tokens (DelimitedBinaryWords.encode input) =
      UnaryFieldEncoderMachine.unaryFields (values input) := by
  rcases input with ⟨words⟩
  change tokens (words.flatMap DelimitedBinaryWords.wordTokens) =
    UnaryFieldEncoderMachine.unaryFields (words.map List.length)
  rw [show tokens (words.flatMap DelimitedBinaryWords.wordTokens) =
      words.flatMap fun word =>
        tokens (DelimitedBinaryWords.wordTokens word) by
    simp [tokens, List.flatMap_assoc]]
  induction words with
  | nil => rfl
  | cons word words induction =>
      simp only [List.flatMap_cons, List.map_cons,
        UnaryFieldEncoderMachine.unaryFields_cons]
      rw [tokens_wordTokens, induction]

noncomputable def tokensComputableInPolyTime :
    TM2ComputableInPolyTime id id tokens :=
  FiniteBlockTransducer.computableInPolyTime tokenBlock

/-- Binary-word lengths are polynomial-time computable as canonical unary
fields. -/
noncomputable def valuesComputableInPolyTime :
    TM2ComputableInPolyTime
      DelimitedBinaryWords.finEncoding.encode
      UnaryFieldEncoderMachine.unaryFields values := by
  let physical : TM2ComputableInPolyTime
      DelimitedBinaryWords.finEncoding.encode id
      (fun input => tokens
        (DelimitedBinaryWords.finEncoding.encode input)) :=
    TM2PolyTimeInputEncodingTransport.of_prepare
      DelimitedBinaryWords.finEncoding.encode
      tokensComputableInPolyTime (fun _ => rfl) (fun _ => rfl)
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq physical
    tokens_encode

end LeanTrominoes.DelimitedBinaryWordLengths

end
