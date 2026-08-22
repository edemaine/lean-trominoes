/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceCycleLinkTargetIndices
import LeanTrominoes.PrefixSums
import LeanTrominoes.UnaryBlockRightRotationMachine

/-! # Cycle-link targets as right-rotated consecutive blocks -/

namespace LeanTrominoes.PeriodicCNF.SourceCycleLinkTargetIndices

@[simp] theorem rotatedBlock_eq_groupTargetIndices
    (blockStart groupSize : Nat) :
    UnaryBlockRightRotationMachine.rotatedBlock blockStart groupSize =
      groupTargetIndices blockStart groupSize := by
  cases groupSize with
  | zero => rfl
  | succ count =>
      rw [UnaryBlockRightRotationMachine.rotatedBlock,
        groupTargetIndices_succ]

theorem rotatedBlocks_prefixStartsAux
    (blockStart : Nat) (groupSizes : List Nat) :
    UnaryBlockRightRotationMachine.rotatedBlocks groupSizes
        (PrefixSums.startsAux blockStart groupSizes) =
      targetIndicesAux blockStart groupSizes := by
  induction groupSizes generalizing blockStart with
  | nil => rfl
  | cons groupSize groupSizes induction =>
      simp only [PrefixSums.startsAux_cons,
        UnaryBlockRightRotationMachine.rotatedBlocks, targetIndicesAux,
        rotatedBlock_eq_groupTargetIndices]
      rw [induction]

/-- Pairing group sizes with their prefix starts gives exactly the complete
cycle-link negative-source target stream. -/
theorem rotatedBlocks_prefixStarts (groupSizes : List Nat) :
    UnaryBlockRightRotationMachine.rotatedBlocks groupSizes
        (PrefixSums.starts groupSizes) =
      targetIndices groupSizes := by
  exact rotatedBlocks_prefixStartsAux 0 groupSizes

end LeanTrominoes.PeriodicCNF.SourceCycleLinkTargetIndices
