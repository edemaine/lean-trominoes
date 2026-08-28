/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordFixedFieldRowExpansionCompiler

/-! # Semantics of fixed-field delimited-row expansion -/

namespace LeanTrominoes
namespace DelimitedBinaryWordFixedFieldRowExpansion

@[simp] theorem expandedBit_length
    (width index : Nat) (bit : Bool) :
    (expandedBit width index bit).length = width := by
  simp [expandedBit]

@[simp] theorem row_length
    (width index : Nat) (bits : List Bool) :
    (row width index bits).length = bits.length * width := by
  unfold row
  induction bits with
  | nil => simp
  | cons bit bits induction =>
      simp [induction, Nat.succ_mul, Nat.add_comm]

/-- Uniform input row lengths remain uniform after every fixed-field
expansion. -/
theorem rows_forall_length (width length : Nat)
    (input : DelimitedBinaryWords.Input)
    (lengths : input.words.Forall fun bits => bits.length = length) :
    (rows width input).words.Forall fun bits =>
      bits.length = length * width := by
  rw [List.forall_iff_forall_mem]
  intro expanded expandedMember
  unfold rows at expandedMember
  rcases List.mem_flatMap.mp expandedMember with
    ⟨bits, bitsMember, expandedMember⟩
  rcases List.mem_map.mp expandedMember with
    ⟨index, _indexMember, expandedEq⟩
  subst expanded
  rw [row_length]
  exact congrArg (fun value => value * width)
    ((List.forall_iff_forall_mem.mp lengths) bits bitsMember)

@[simp] theorem rowTokens_wordTokens
    (width index : Nat) (bits : List Bool) :
    rowTokens width index (DelimitedBinaryWords.wordTokens bits) =
      DelimitedBinaryWords.wordTokens (row width index bits) := by
  have bitTokens :
      (bits.map DelimitedBinaryWords.Token.bit).flatMap
          (tokenBlock width index) =
        (bits.flatMap (expandedBit width index)).map
          DelimitedBinaryWords.Token.bit := by
    induction bits with
    | nil => rfl
    | cons bit bits induction =>
        simp [tokenBlock, induction, List.map_append]
  unfold rowTokens DelimitedBinaryWords.wordTokens row
  simp [tokenBlock, bitTokens]

@[simp] theorem rowCopiesFor_wordTokens
    (width : Nat) (indices : List Nat) (bits : List Bool) :
    rowCopiesFor width indices (DelimitedBinaryWords.wordTokens bits) =
      DelimitedBinaryWords.encode
        ⟨indices.map fun index => row width index bits⟩ := by
  unfold rowCopiesFor DelimitedBinaryWords.encode
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro index _indexMember
  exact rowTokens_wordTokens width index bits

@[simp] theorem rowCopies_wordTokens
    (width : Nat) (bits : List Bool) :
    rowCopies width (DelimitedBinaryWords.wordTokens bits) =
      DelimitedBinaryWords.encode
        ⟨(List.range width).map fun index => row width index bits⟩ := by
  unfold rowCopies
  exact rowCopiesFor_wordTokens width (List.range width) bits

/-- The block mapper returns exactly all fixed-field expansions of every
input row, in input-row then field order. -/
@[simp] theorem tokens_encode (width : Nat)
    (input : DelimitedBinaryWords.Input) :
    tokens width (DelimitedBinaryWords.encode input) =
      DelimitedBinaryWords.encode (rows width input) := by
  unfold tokens rows
  rw [DelimitedBinaryWords.mappedOutput_encode]
  unfold DelimitedBinaryWords.encode
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro bits _bitsMember
  exact rowCopies_wordTokens width bits

end DelimitedBinaryWordFixedFieldRowExpansion
end LeanTrominoes
