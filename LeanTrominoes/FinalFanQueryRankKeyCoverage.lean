/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalFanQueryKeyCompiler
import LeanTrominoes.StableOccurrenceRankCandidateKeys

/-! # Coverage of finite fan rank keys -/

namespace LeanTrominoes.FinalFanQueryRanks

/-- Semantic composite keys requested by all three finite fan slots of every
presented occurrence. -/
def keyedBlocks (values : List Nat) : List Nat :=
  values.flatMap fun value =>
    (block (BoundedPositiveCountPreds.boundedPositiveCountPred
      (values.count value))).map fun rank => value * 3 + rank.val

/-- Every selected active-or-fallback rank is below the positive multiplicity
from which its fan count predecessor was computed. -/
theorem selectedRank_val_lt_count
    (count : Nat) (positive : 0 < count) (slot : Fin 3) :
    (selectedRank
      (BoundedPositiveCountPreds.boundedPositiveCountPred count) slot).val <
        count := by
  cases count with
  | zero => omega
  | succ count =>
      cases count with
      | zero =>
          change (selectedRank 0 slot).val < 1
          unfold selectedRank
          split <;> omega
      | succ count =>
          cases count with
          | zero =>
              change (selectedRank 1 slot).val < 2
              unfold selectedRank
              split <;> omega
          | succ count =>
              exact lt_of_lt_of_le
                (selectedRank
                  (BoundedPositiveCountPreds.boundedPositiveCountPred
                    (count + 3)) slot).isLt (by omega)

/-- Every semantic finite-fan query is covered by the stable occurrence-key
column of the same values. -/
theorem keyedBlocks_subset_candidateKeys (values : List Nat) :
    keyedBlocks values ⊆ StableOccurrenceRanks.candidateKeys values := by
  intro query queryMember
  rcases List.mem_flatMap.mp queryMember with
    ⟨value, valueMember, queryMember⟩
  rcases List.mem_map.mp queryMember with
    ⟨selectedRank, selectedRankMember, rfl⟩
  unfold block at selectedRankMember
  rcases List.mem_map.mp selectedRankMember with
    ⟨slot, _slotMember, rfl⟩
  apply StableOccurrenceRanks.candidateKey_mem_of_rank_lt_count
  exact selectedRank_val_lt_count (values.count value)
    (List.count_pos_iff.mpr valueMember) slot

end LeanTrominoes.FinalFanQueryRanks
