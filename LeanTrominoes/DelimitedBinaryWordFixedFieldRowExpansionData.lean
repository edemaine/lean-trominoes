/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordBlockMapSemantics

/-! # Fixed-field expansion of delimited Boolean rows -/

namespace LeanTrominoes
namespace DelimitedBinaryWordFixedFieldRowExpansion

/-- Replace one row bit by a fixed-width block carrying that bit at exactly
one field position. -/
def expandedBit (width index : Nat) (bit : Bool) : List Bool :=
  match width, index with
  | 0, _ => []
  | width + 1, 0 => bit :: List.replicate width false
  | width + 1, index + 1 => false :: expandedBit width index bit

/-- Expand every bit of a row into the selected fixed field position. -/
def row (width index : Nat) (bits : List Bool) : List Bool :=
  bits.flatMap (expandedBit width index)

/-- Token-level version of one selected-field row expansion. -/
def tokenBlock (width index : Nat) :
    DelimitedBinaryWords.Token → List DelimitedBinaryWords.Token
  | .wordStart => [.wordStart]
  | .bit bit => (expandedBit width index bit).map .bit
  | .wordEnd => [.wordEnd]

def rowTokens (width index : Nat)
    (source : List DelimitedBinaryWords.Token) :
    List DelimitedBinaryWords.Token :=
  source.flatMap (tokenBlock width index)

/-- Emit one expanded row for every field position. -/
def rowCopiesFor (width : Nat) (indices : List Nat)
    (source : List DelimitedBinaryWords.Token) :
    List DelimitedBinaryWords.Token :=
  indices.flatMap fun index => rowTokens width index source

def rowCopies (width : Nat)
    (source : List DelimitedBinaryWords.Token) :
    List DelimitedBinaryWords.Token :=
  rowCopiesFor width (List.range width) source

/-- Expand every delimited row independently into all fixed field rows. -/
def tokens (width : Nat) (source : List DelimitedBinaryWords.Token) :
    List DelimitedBinaryWords.Token :=
  TM2EndDelimitedBlockMap.mappedOutput
    DelimitedBinaryWords.isWordEnd (rowCopies width) source

/-- Semantic row list emitted by the token-level expansion. -/
def rows (width : Nat) (input : DelimitedBinaryWords.Input) :
    DelimitedBinaryWords.Input :=
  ⟨input.words.flatMap fun bits =>
    (List.range width).map fun index => row width index bits⟩

end DelimitedBinaryWordFixedFieldRowExpansion
end LeanTrominoes
