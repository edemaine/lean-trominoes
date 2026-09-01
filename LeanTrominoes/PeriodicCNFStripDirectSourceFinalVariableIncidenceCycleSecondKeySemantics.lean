/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListZipWithThreeAlignedChoice
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedNextOccurrenceKeyCyclicSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableFanSlotCountKeySemantics

/-! # Second cycle references in variable-incidence blocks -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

def groupedVariableIncidenceCycleSecondKey
    (pair : GroupedVariableFanSlot) (current next : Nat) : Nat :=
  if pair.1.countPred = 0 then current else next

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- In a one-occurrence fan the cyclic successor is the current key, so the
local one-occurrence fallback may uniformly be read as the compiled successor
column. -/
theorem directSourceFinalGroupedCycleSecondKeys_eq_nextKeys
    (symbols : List encoding.Γ) :
    List.zipWith3 groupedVariableIncidenceCycleSecondKey
        (directSourceFinalGroupedVariableFanSlots decider symbols)
        (directSourceFinalUniqueFanQueryKeys decider symbols)
        (directSourceFinalGroupedNextOccurrenceKeys decider symbols) =
      directSourceFinalGroupedNextOccurrenceKeys decider symbols := by
  rw [directSourceFinalGroupedNextOccurrenceKeys_eq_map_cyclic]
  apply List.zipWith3_choose_eq_map
    (fun pair : GroupedVariableFanSlot => pair.1.countPred)
    (fun key => BoundedPositiveCountPreds.boundedPositiveCountPred
      ((directSourceFinalAtomIdentityCodes decider symbols).count
        (key / 3))) 0
    (StableOccurrenceRanks.cyclicSuccessorKey
      (directSourceFinalAtomIdentityCodes decider symbols))
  · exact directSourceFinalGroupedVariableFanSlotCountPreds_eq_map_countPred
      decider symbols
  · intro key keyMember countPredZero
    let values := directSourceFinalAtomIdentityCodes decider symbols
    have keyCandidate : key ∈ StableOccurrenceRanks.candidateKeys values := by
      rw [← directSourceFinalOccurrenceCandidateKeys_eq_candidateKeys]
      exact directSourceFinalUniqueFanQueryKey_mem_candidateKeys
        decider symbols key keyMember
    rcases (StableOccurrenceRanks.mem_candidateKeys_iff values key).mp
        keyCandidate with
      ⟨value, rank, valueMember, rankLt, keyEq⟩
    have countLe : values.count value ≤ 3 :=
      directSourceFinalAtomIdentityCodes_count_le_three
        decider symbols value
    have rankThree : rank < 3 := lt_of_lt_of_le rankLt countLe
    have valueEq : value = key / 3 := by omega
    have countPositive : 0 < values.count (key / 3) := by
      rw [← valueEq]
      exact List.count_pos_iff.mpr valueMember
    have countAtMostThree : values.count (key / 3) ≤ 3 :=
      directSourceFinalAtomIdentityCodes_count_le_three
        decider symbols (key / 3)
    have countEq : values.count (key / 3) = 1 := by
      have recoverCount :=
        BoundedPositiveCountPreds.boundedPositiveCountPred_add_one_of_pos_le_three
          (values.count (key / 3)) countPositive countAtMostThree
      have countPredValueZero :
          (BoundedPositiveCountPreds.boundedPositiveCountPred
            (values.count (key / 3))).val = 0 := by
        exact congrArg Fin.val countPredZero
      rw [countPredValueZero] at recoverCount
      omega
    have valueCountEq : values.count value = 1 := by
      rw [valueEq]
      exact countEq
    have rankEqZero : rank = 0 := by omega
    change (key / 3) * 3 +
      ((key % 3 + 1) % values.count (key / 3)) = key
    rw [countEq]
    simp only [Nat.mod_one, Nat.add_zero]
    omega

end LeanTrominoes.PeriodicCNFStripReduction

end
