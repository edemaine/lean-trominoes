/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWords
import LeanTrominoes.PeriodicCNFSourceOccurrenceAtomPairData

/-! # Delimited atom words extracted from source occurrence tokens -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace SourceOccurrenceAtomWords

open Turing

/-- Fixed physical translation from the occurrence-token grammar to the
subword carrying each atom. -/
def block : SourceOccurrenceTokens.Token →
    List DelimitedBinaryWords.Token
  | .literal _ => [.wordStart]
  | .atomBit bit => [.bit bit]
  | .atomEnd => [.wordEnd]
  | _ => []

def tokens (source : List SourceOccurrenceTokens.Token) :
    List DelimitedBinaryWords.Token :=
  source.flatMap block

@[simp] theorem tokens_nil : tokens [] = [] := rfl

theorem tokens_append
    (first second : List SourceOccurrenceTokens.Token) :
    tokens (first ++ second) = tokens first ++ tokens second := by
  simp [tokens]

theorem tokens_atomTokens (atom : Nat) :
    tokens (SourceOccurrenceTokens.atomTokens atom) =
      (SourceOccurrenceAtomPairs.atomWord atom).map
        DelimitedBinaryWords.Token.bit := by
  unfold tokens SourceOccurrenceTokens.atomTokens
    SourceOccurrenceAtomPairs.atomWord
  rw [List.flatMap_map, List.map_map]
  change List.flatMap
      (fun symbol =>
        [DelimitedBinaryWords.Token.bit
          (SourceOccurrenceTokens.nativeBit symbol)])
      (PartrecToTM2.trNat atom) = _
  rw [← List.map_eq_flatMap]
  rfl

@[simp] theorem tokens_offsetTokens (offset : Int) :
    tokens (SourceOccurrenceTokens.offsetTokens offset) = [] := by
  unfold tokens SourceOccurrenceTokens.offsetTokens
  rw [List.flatMap_map]
  simp [block]

theorem tokens_literalTokens (index : Nat)
    (literal : PeriodicLiteral Nat) :
    tokens (SourceOccurrenceTokens.literalTokens index literal) =
      DelimitedBinaryWords.wordTokens
        (SourceOccurrenceAtomPairs.atomWord literal.atom) := by
  unfold SourceOccurrenceTokens.literalTokens
    DelimitedBinaryWords.wordTokens
  rw [tokens_append, tokens_append, tokens_append,
    tokens_append, tokens_atomTokens, tokens_offsetTokens]
  simp [tokens, block]

end SourceOccurrenceAtomWords
end PeriodicCNF
end LeanTrominoes
