/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairs
import LeanTrominoes.DelimitedBinaryWords
import LeanTrominoes.TM2EndDelimitedBlockMapData

/-! # Four-word expansion of binary-word pairs -/

namespace LeanTrominoes.DelimitedBinaryWordPairFourWordExpansion

abbrev PairToken := DelimitedBinaryWordPairs.Token
abbrev WordToken := DelimitedBinaryWords.Token

/-- Translate one pair token to its contribution to the adjacent two-word
encoding of that pair. -/
def componentBlock : PairToken → List WordToken
  | .pairStart => [.wordStart]
  | .firstBit bit => [.bit bit]
  | .middle => [.wordEnd, .wordStart]
  | .secondBit bit => [.bit bit]
  | .pairEnd => [.wordEnd]

def componentTokens (source : List PairToken) : List WordToken :=
  source.flatMap componentBlock

/-- Duplicate one complete pair's adjacent two-word encoding. -/
def duplicatedComponentTokens (source : List PairToken) : List WordToken :=
  componentTokens source ++ componentTokens source

def isPairEnd : PairToken → Bool
  | .pairEnd => true
  | _ => false

/-- Run the local duplication independently on every complete pair. -/
def tokens (source : List PairToken) : List WordToken :=
  TM2EndDelimitedBlockMap.mappedOutput
    isPairEnd duplicatedComponentTokens source

/-- Semantic four-word block of each input pair. -/
def expandedInput (input : DelimitedBinaryWordPairs.Input) :
    DelimitedBinaryWords.Input :=
  ⟨input.pairs.flatMap fun pair =>
    [pair.1, pair.2, pair.1, pair.2]⟩

end LeanTrominoes.DelimitedBinaryWordPairFourWordExpansion
