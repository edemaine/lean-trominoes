/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairBooleanFilterCompiler
import LeanTrominoes.DelimitedBinaryWords
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2PolyTimeInputEncodingTransport
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Boolean filtering of delimited binary words -/

noncomputable section

namespace LeanTrominoes.DelimitedBinaryWordBooleanFilter

open Computability Turing

abbrev WordToken := DelimitedBinaryWords.Token
abbrev PairToken := DelimitedBinaryWordPairs.Token

/-- Regard every word as the first component of a pair whose second component
is empty. -/
def emptySecondPairs (input : DelimitedBinaryWords.Input) :
    DelimitedBinaryWordPairs.Input :=
  ⟨input.words.map fun word => (word, [])⟩

def toPairBlock : WordToken → List PairToken
  | .wordStart => [.pairStart]
  | .bit bit => [.firstBit bit]
  | .wordEnd => [.middle, .pairEnd]

def toPairTokens (source : List WordToken) : List PairToken :=
  source.flatMap toPairBlock

private theorem flatMap_singletons_eq_map
    {Source Target : Type*} (function : Source → Target)
    (values : List Source) :
    values.flatMap (fun value => [function value]) =
      values.map function := by
  induction values with
  | nil => rfl
  | cons value values induction => simp [induction]

@[simp] theorem toPairTokens_wordTokens (word : List Bool) :
    toPairTokens (DelimitedBinaryWords.wordTokens word) =
      DelimitedBinaryWordPairs.pairTokens (word, []) := by
  have bits :
      (word.map DelimitedBinaryWords.Token.bit).flatMap toPairBlock =
        word.map DelimitedBinaryWordPairs.Token.firstBit := by
    rw [List.flatMap_map]
    exact flatMap_singletons_eq_map
      DelimitedBinaryWordPairs.Token.firstBit word
  simp [DelimitedBinaryWords.wordTokens, toPairTokens, toPairBlock,
    DelimitedBinaryWordPairs.pairTokens, bits]

@[simp] theorem toPairTokens_encode (input : DelimitedBinaryWords.Input) :
    toPairTokens (DelimitedBinaryWords.encode input) =
      DelimitedBinaryWordPairs.encode (emptySecondPairs input) := by
  rcases input with ⟨words⟩
  unfold DelimitedBinaryWords.encode DelimitedBinaryWordPairs.encode
    emptySecondPairs toPairTokens
  rw [List.flatMap_assoc]
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro word _wordMember
  exact toPairTokens_wordTokens word

noncomputable def toPairTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id toPairTokens :=
  FiniteBlockTransducer.computableInPolyTime toPairBlock

/-- Canonical word inputs can be converted to canonical empty-second pair
inputs in polynomial time. -/
noncomputable def emptySecondPairsComputableInPolyTime :
    @TM2ComputableInPolyTime
      DelimitedBinaryWords.Input DelimitedBinaryWordPairs.Input
      WordToken PairToken
      DelimitedBinaryWords.finEncoding.encode
      DelimitedBinaryWordPairs.finEncoding.encode emptySecondPairs := by
  let physical : TM2ComputableInPolyTime
      DelimitedBinaryWords.finEncoding.encode id
      (fun input => toPairTokens
        (DelimitedBinaryWords.finEncoding.encode input)) :=
    TM2PolyTimeInputEncodingTransport.of_prepare
      DelimitedBinaryWords.finEncoding.encode
      toPairTokensComputableInPolyTime (fun _ => rfl) (fun _ => rfl)
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    physical fun input => by
      rw [DelimitedBinaryWords.finEncoding_encode, toPairTokens_encode]
      exact (DelimitedBinaryWordPairs.finEncoding_encode _).symm

/-- Project the first word of every canonical pair. -/
def firstWords (input : DelimitedBinaryWordPairs.Input) :
    DelimitedBinaryWords.Input :=
  ⟨input.pairs.map Prod.fst⟩

def firstBlock : PairToken → List WordToken
  | .pairStart => [.wordStart]
  | .firstBit bit => [.bit bit]
  | .middle => [.wordEnd]
  | .secondBit _ => []
  | .pairEnd => []

def firstTokens (source : List PairToken) : List WordToken :=
  source.flatMap firstBlock

@[simp] theorem firstTokens_pairTokens
    (pair : List Bool × List Bool) :
    firstTokens (DelimitedBinaryWordPairs.pairTokens pair) =
      DelimitedBinaryWords.wordTokens pair.1 := by
  rcases pair with ⟨first, second⟩
  have firstBits :
      (first.map DelimitedBinaryWordPairs.Token.firstBit).flatMap firstBlock =
        first.map DelimitedBinaryWords.Token.bit := by
    rw [List.flatMap_map]
    exact flatMap_singletons_eq_map DelimitedBinaryWords.Token.bit first
  have secondBits :
      (second.map DelimitedBinaryWordPairs.Token.secondBit).flatMap
          firstBlock = [] := by
    rw [List.flatMap_map]
    simp [firstBlock]
  simp [firstTokens, firstBlock,
    DelimitedBinaryWordPairs.pairTokens,
    DelimitedBinaryWords.wordTokens, firstBits, secondBits]

@[simp] theorem firstTokens_encode
    (input : DelimitedBinaryWordPairs.Input) :
    firstTokens (DelimitedBinaryWordPairs.encode input) =
      DelimitedBinaryWords.encode (firstWords input) := by
  rcases input with ⟨pairs⟩
  unfold DelimitedBinaryWordPairs.encode DelimitedBinaryWords.encode
    firstWords firstTokens
  rw [List.flatMap_assoc]
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro pair _pairMember
  exact firstTokens_pairTokens pair

noncomputable def firstTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id firstTokens :=
  FiniteBlockTransducer.computableInPolyTime firstBlock

noncomputable def firstWordsComputableInPolyTime :
    @TM2ComputableInPolyTime
      DelimitedBinaryWordPairs.Input DelimitedBinaryWords.Input
      PairToken WordToken
      DelimitedBinaryWordPairs.finEncoding.encode
      DelimitedBinaryWords.finEncoding.encode firstWords := by
  let physical : TM2ComputableInPolyTime
      DelimitedBinaryWordPairs.finEncoding.encode id
      (fun input => firstTokens
        (DelimitedBinaryWordPairs.finEncoding.encode input)) :=
    TM2PolyTimeInputEncodingTransport.of_prepare
      DelimitedBinaryWordPairs.finEncoding.encode
      firstTokensComputableInPolyTime (fun _ => rfl) (fun _ => rfl)
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    physical fun input => by
      rw [DelimitedBinaryWordPairs.finEncoding_encode, firstTokens_encode]
      exact (DelimitedBinaryWords.finEncoding_encode _).symm

/-- Retain exactly the words whose aligned Boolean controls are true.  Extra
controls and extra words are ignored. -/
def selectedWords (controls : List Bool)
    (input : DelimitedBinaryWords.Input) : DelimitedBinaryWords.Input :=
  firstWords
    ⟨DelimitedBinaryWordPairBooleanFilter.selectedPairs controls
      (emptySecondPairs input).pairs⟩

/-- Any compiled word stream can be filtered by any compiled aligned Boolean
stream in polynomial time. -/
noncomputable def selectedWordsComputableInPolyTime
    {Source InputSymbol : Type}
    [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeSource : Source → List InputSymbol)
    (controls : Source → List Bool)
    (words : Source → DelimitedBinaryWords.Input)
    (controlCompiler : TM2ComputableInPolyTime encodeSource id controls)
    (wordCompiler : TM2ComputableInPolyTime encodeSource
      DelimitedBinaryWords.finEncoding.encode words) :
    TM2ComputableInPolyTime encodeSource
      DelimitedBinaryWords.finEncoding.encode
      (fun source => selectedWords (controls source) (words source)) := by
  let pairCompiler := TM2CompositionMachine.computableInPolyTime
    wordCompiler emptySecondPairsComputableInPolyTime
  let filtered :=
    DelimitedBinaryWordPairBooleanFilter.filteredPairsComputableInPolyTime
      encodeSource controls (fun source => emptySecondPairs (words source))
      controlCompiler pairCompiler
  exact TM2CompositionMachine.computableInPolyTime
    filtered firstWordsComputableInPolyTime

end LeanTrominoes.DelimitedBinaryWordBooleanFilter

end
