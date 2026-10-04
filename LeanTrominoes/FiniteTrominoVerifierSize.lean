/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteTrominoVerifierBackend
import LeanTrominoes.FiniteExactCoverVerifierSize

/-! # Serialized bounds for the geometric verifier backend

There are at most 24 candidates per listed cell, each with three cells.
The prefill's serialized size is retained separately, including malformed
preplacements that the verifier must reject.
-/
namespace LeanTrominoes.Tromino.FiniteVerifier

theorem footprint_word_lengths (tile : Finset Cell) (wordBudget : Nat)
    (bounded : ∀ cell∈tile, (cellWord cell).length≤wordBudget) :
    ∀ word∈footprintWords tile, word.length≤wordBudget := by
  intro word member
  obtain ⟨cell,hc,rfl⟩ := word_of_footprint tile word member
  exact bounded cell hc

theorem candidate_block_bounds (t : Tromino) (cells : List Cell) (wordBudget : Nat)
    (bounded : ∀ tile∈FiniteWitness.candidates t cells.toFinset,
      ∀ cell∈tile, (cellWord cell).length≤wordBudget) :
    ∀ block∈(candidateTiles t cells).map footprintWords,
      block.length≤3 ∧ ∀ word∈block, word.length≤wordBudget := by
  intro block member
  obtain ⟨tile,ht,rfl⟩ := List.mem_map.mp member
  have candidate := (mem_candidateTiles t cells tile).mp ht
  obtain ⟨placement,equal⟩ := ((FiniteWitness.mem_candidates t cells.toFinset tile).mp candidate).1
  refine ⟨?_,footprint_word_lengths tile wordBudget (bounded tile candidate)⟩
  rw [footprintWords_length,← equal,Tromino.card_placement_cells]

theorem nativeRequest_encode_length_le (t : Tromino) (cells : List Cell)
    (prefill : List (Finset Cell)) (bits : List Bool) (wordBudget : Nat)
    (region : ∀ cell∈cells, (cellWord cell).length≤wordBudget)
    (candidates : ∀ tile∈FiniteWitness.candidates t cells.toFinset,
      ∀ cell∈tile, (cellWord cell).length≤wordBudget) :
    (nativeRequest t cells prefill bits).encode.length≤
      (145*wordBudget+338)*cells.length+
        FiniteExactCoverVerifier.blockSize (prefill.map footprintWords)+bits.length := by
  rw [FiniteExactCoverVerifier.Request.encode_length]
  have regionSize := FiniteExactCoverVerifier.wordSize_le (cells.map cellWord) wordBudget
    (by
      intro word member
      obtain ⟨cell,hc,rfl⟩ := List.mem_map.mp member
      exact region cell hc)
  have candidateSize := FiniteExactCoverVerifier.blockSize_le
    ((candidateTiles t cells).map footprintWords) wordBudget 3
    (candidate_block_bounds t cells wordBudget candidates)
  have count := candidateTiles_length_le t cells
  simp only [List.length_map] at regionSize candidateSize
  have candidateBound := Nat.mul_le_mul_left (2*(wordBudget+2)*3+2) count
  change FiniteExactCoverVerifier.wordSize (cells.map cellWord)+
    FiniteExactCoverVerifier.blockSize ((candidateTiles t cells).map footprintWords)+
      FiniteExactCoverVerifier.blockSize (prefill.map footprintWords)+bits.length≤_
  nlinarith

end LeanTrominoes.Tromino.FiniteVerifier
