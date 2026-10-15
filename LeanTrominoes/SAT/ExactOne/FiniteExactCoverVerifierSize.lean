/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.ExactOne.FiniteExactCoverVerifier

/-! # Explicit size of exact-cover verifier requests -/
namespace LeanTrominoes.FiniteExactCoverVerifier

def wordSize (words : Block) : Nat := (words.map List.length).sum+2*words.length

theorem wordSize_eq (words : Block) :
    wordSize words=(DelimitedBinaryWords.encode ⟨words⟩).length := by
  induction words with
  | nil => rfl
  | cons word words ih =>
    simp [wordSize,DelimitedBinaryWords.encode,DelimitedBinaryWords.wordTokens] at *
    omega

def blockSize (blocks : List Block) : Nat :=
  (blocks.map fun block => 2*wordSize block+2).sum

theorem blockSize_eq (blocks : List Block) :
    blockSize blocks=(DelimitedBinaryWords.encode ⟨blocks.map BinaryWordBlocks.pack⟩).length := by
  induction blocks with
  | nil => rfl
  | cons block blocks ih =>
    have packSize := BinaryWordBlocks.pack_length block
    rw [← wordSize_eq] at packSize
    change 2*wordSize block+2+blockSize blocks=
      (DelimitedBinaryWords.wordTokens (BinaryWordBlocks.pack block) ++
        DelimitedBinaryWords.encode ⟨blocks.map BinaryWordBlocks.pack⟩).length
    rw [ih]
    simp only [DelimitedBinaryWords.wordTokens,List.length_append,List.length_cons,
      List.length_map,List.length_nil,packSize]

theorem Request.encode_length (request : Request) :
    request.encode.length=wordSize request.region+blockSize request.candidates+
      blockSize request.required+request.bits.length := by
  simp [Request.encode,wordSize_eq,blockSize_eq,Nat.add_assoc]

theorem wordSize_le (words : Block) (wordBudget : Nat)
    (bounded : ∀ word∈words, word.length≤wordBudget) :
    wordSize words≤(wordBudget+2)*words.length := by
  induction words with
  | nil => simp [wordSize]
  | cons word words ih =>
    have head := bounded word (by simp)
    have tail := ih (fun other member => bounded other (by simp [member]))
    simp [wordSize] at *
    nlinarith

theorem blockSize_le (blocks : List Block) (wordBudget cellBudget : Nat)
    (bounded : ∀ block∈blocks, block.length≤cellBudget ∧ ∀ word∈block, word.length≤wordBudget) :
    blockSize blocks≤(2*(wordBudget+2)*cellBudget+2)*blocks.length := by
  induction blocks with
  | nil => simp [blockSize]
  | cons block blocks ih =>
    have head := bounded block (by simp)
    have headSize := (wordSize_le block wordBudget head.2).trans
      (Nat.mul_le_mul_left (wordBudget+2) head.1)
    have tail := ih (fun other member => bounded other (by simp [member]))
    simp only [blockSize,List.map_cons,List.sum_cons,List.length_cons] at *
    nlinarith

/-- In particular, fixed-size footprints have a linear serialized-table
bound in the number of candidates and the maximum cell-name width. -/
theorem Request.encode_length_le (request : Request) (wordBudget cellBudget : Nat)
    (region : ∀ word∈request.region, word.length≤wordBudget)
    (candidates : ∀ block∈request.candidates,
      block.length≤cellBudget ∧ ∀ word∈block, word.length≤wordBudget)
    (required : ∀ block∈request.required,
      block.length≤cellBudget ∧ ∀ word∈block, word.length≤wordBudget) :
    request.encode.length≤(wordBudget+2)*request.region.length+
      (2*(wordBudget+2)*cellBudget+2)*(request.candidates.length+request.required.length)+
      request.bits.length := by
  rw [request.encode_length]
  have regionSize := wordSize_le request.region wordBudget region
  have candidateSize := blockSize_le request.candidates wordBudget cellBudget candidates
  have requiredSize := blockSize_le request.required wordBudget cellBudget required
  nlinarith

end LeanTrominoes.FiniteExactCoverVerifier
