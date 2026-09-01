/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordLengthsCompiler
import LeanTrominoes.DelimitedBinaryWordPairs
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2PolyTimeInputEncodingTransport
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Second-word projection from delimited binary-word pairs -/

noncomputable section

namespace LeanTrominoes.DelimitedBinaryWordPairSecondWords

open Computability Turing

abbrev PairToken := DelimitedBinaryWordPairs.Token
abbrev WordToken := DelimitedBinaryWords.Token

def words (input : DelimitedBinaryWordPairs.Input) :
    DelimitedBinaryWords.Input :=
  ⟨input.pairs.map Prod.snd⟩

def tokenBlock : PairToken → List WordToken
  | .pairStart => []
  | .firstBit _ => []
  | .middle => [.wordStart]
  | .secondBit bit => [.bit bit]
  | .pairEnd => [.wordEnd]

def tokens (source : List PairToken) : List WordToken :=
  source.flatMap tokenBlock

private theorem flatMap_firstBits (word : List Bool) :
    (word.map DelimitedBinaryWordPairs.Token.firstBit).flatMap tokenBlock =
      [] := by
  induction word with
  | nil => rfl
  | cons bit word induction => simp [tokenBlock, induction]

private theorem flatMap_secondBits (word : List Bool) :
    (word.map DelimitedBinaryWordPairs.Token.secondBit).flatMap tokenBlock =
      word.map DelimitedBinaryWords.Token.bit := by
  induction word with
  | nil => rfl
  | cons bit word induction => simp [tokenBlock, induction]

@[simp] theorem tokens_pairTokens (pair : List Bool × List Bool) :
    tokens (DelimitedBinaryWordPairs.pairTokens pair) =
      DelimitedBinaryWords.wordTokens pair.2 := by
  rcases pair with ⟨first, second⟩
  simp [tokens, tokenBlock, DelimitedBinaryWordPairs.pairTokens,
    DelimitedBinaryWords.wordTokens, flatMap_firstBits,
    flatMap_secondBits]

@[simp] theorem tokens_encode (input : DelimitedBinaryWordPairs.Input) :
    tokens (DelimitedBinaryWordPairs.encode input) =
      DelimitedBinaryWords.encode (words input) := by
  rcases input with ⟨pairs⟩
  unfold DelimitedBinaryWordPairs.encode DelimitedBinaryWords.encode
    words tokens
  rw [List.flatMap_assoc, List.flatMap_map]
  apply List.flatMap_congr
  intro pair _
  exact tokens_pairTokens pair

noncomputable def tokensComputableInPolyTime :
    TM2ComputableInPolyTime id id tokens :=
  FiniteBlockTransducer.computableInPolyTime tokenBlock

noncomputable def wordsComputableInPolyTime :
    TM2ComputableInPolyTime
      DelimitedBinaryWordPairs.finEncoding.encode
      DelimitedBinaryWords.finEncoding.encode words := by
  let physical : TM2ComputableInPolyTime
      DelimitedBinaryWordPairs.finEncoding.encode id
      (fun input => tokens
        (DelimitedBinaryWordPairs.finEncoding.encode input)) :=
    TM2PolyTimeInputEncodingTransport.of_prepare
      DelimitedBinaryWordPairs.finEncoding.encode
      tokensComputableInPolyTime (fun _ => rfl) (fun _ => rfl)
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq physical
    fun input => by
      rw [DelimitedBinaryWordPairs.finEncoding_encode, tokens_encode]
      exact (DelimitedBinaryWords.finEncoding_encode _).symm

/-- The lengths of all second words, in pair order. -/
def lengths (input : DelimitedBinaryWordPairs.Input) : List Nat :=
  DelimitedBinaryWordLengths.values (words input)

noncomputable def lengthsComputableInPolyTime :
    TM2ComputableInPolyTime
      DelimitedBinaryWordPairs.finEncoding.encode
      UnaryFieldEncoderMachine.unaryFields lengths := by
  unfold lengths
  exact TM2CompositionMachine.computableInPolyTime
    wordsComputableInPolyTime
    DelimitedBinaryWordLengths.valuesComputableInPolyTime

end LeanTrominoes.DelimitedBinaryWordPairSecondWords

end
