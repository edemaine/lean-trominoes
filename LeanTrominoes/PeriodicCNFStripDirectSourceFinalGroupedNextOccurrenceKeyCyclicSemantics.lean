/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedNextOccurrenceKeySemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedOccurrenceSlotKeySemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedScaledAtomIdentityCodeSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableFanCountKeySemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalUniqueFanQueryKeyPermutation
import LeanTrominoes.StableOccurrenceRankCyclicSuccessorPermutation

/-! # Cyclic semantics of grouped successor occurrence keys -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicOneInThreeToThreeDM
open PeriodicPlanarOneInThreeToThreeDM

@[simp] theorem groupedVariableNextOccurrenceRank_fan_genericSlot
    (fan : VariableRibbonFanData)
    (slot : PeriodicOneInThreeToThreeDM.OccurrenceSlot) :
    groupedVariableNextOccurrenceRank
        (fan, groupedVariableFanGenericSlot slot) =
      (slot.index + 1) % fan.count := by
  cases slot <;> rfl

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- Every compiled grouped successor rank is the cyclic successor of the
base-three remainder of its aligned current key. -/
theorem directSourceFinalGroupedNextOccurrenceRanks_eq_map_cyclic
    (symbols : List encoding.Γ) :
    directSourceFinalGroupedNextOccurrenceRanks decider symbols =
      (directSourceFinalUniqueFanQueryKeys decider symbols).map fun key =>
        (key % 3 + 1) %
          (directSourceFinalAtomIdentityCodes decider symbols).count
            (key / 3) := by
  rw [directSourceFinalGroupedNextOccurrenceRanks_eq_map,
    directSourceFinalGroupedVariableFanSlots_eq_zipWith,
    List.map_zipWith]
  simp only [groupedVariableNextOccurrenceRank_fan_genericSlot]
  have projected :
      List.zipWith
          (fun fan slot => (slot.index + 1) % fan.count)
          (directSourceFinalGroupedVariableFanData decider symbols)
          (directSourceFinalGroupedOccurrenceSlots decider symbols) =
        List.zipWith
          (fun count slot => (slot.index + 1) % count)
          ((directSourceFinalGroupedVariableFanData
            decider symbols).map VariableRibbonFanData.count)
          (directSourceFinalGroupedOccurrenceSlots decider symbols) := by
    rw [List.zipWith_map_left]
  rw [projected,
    directSourceFinalGroupedVariableFanCounts_eq_map_count,
    directSourceFinalGroupedOccurrenceSlots_eq_map_mod,
    List.zipWith_map, List.zipWith_self]
  apply List.map_congr_left
  intro key _keyMember
  rw [BoundedOccurrenceSlots.boundedOccurrenceSlot_index_of_lt_three
    (key % 3) (Nat.mod_lt key (by decide))]

/-- The compiled successor-key column is exactly the generic cyclic map of
the grouped current-key column. -/
theorem directSourceFinalGroupedNextOccurrenceKeys_eq_map_cyclic
    (symbols : List encoding.Γ) :
    directSourceFinalGroupedNextOccurrenceKeys decider symbols =
      (directSourceFinalUniqueFanQueryKeys decider symbols).map
        (StableOccurrenceRanks.cyclicSuccessorKey
          (directSourceFinalAtomIdentityCodes decider symbols)) := by
  rw [directSourceFinalGroupedNextOccurrenceKeys_eq_zipWith,
    directSourceFinalGroupedScaledAtomIdentityCodes_eq_map_div,
    directSourceFinalGroupedNextOccurrenceRanks_eq_map_cyclic,
    List.zipWith_map, List.zipWith_self]
  rfl

/-- Cyclic successor compilation permutes the current occurrence-key column. -/
theorem directSourceFinalGroupedNextOccurrenceKeys_perm_currentKeys
    (symbols : List encoding.Γ) :
    (directSourceFinalGroupedNextOccurrenceKeys decider symbols).Perm
      (directSourceFinalUniqueFanQueryKeys decider symbols) := by
  rw [directSourceFinalGroupedNextOccurrenceKeys_eq_map_cyclic]
  let values := directSourceFinalAtomIdentityCodes decider symbols
  let current := directSourceFinalUniqueFanQueryKeys decider symbols
  let candidates := directSourceFinalOccurrenceCandidateKeys decider symbols
  have currentCandidates : current.Perm candidates :=
    directSourceFinalUniqueFanQueryKeys_perm_candidateKeys decider symbols
  calc
    (current.map
      (StableOccurrenceRanks.cyclicSuccessorKey values)).Perm
        (candidates.map
          (StableOccurrenceRanks.cyclicSuccessorKey values)) :=
      currentCandidates.map _
    _ = (StableOccurrenceRanks.candidateKeys values).map
          (StableOccurrenceRanks.cyclicSuccessorKey values) := by
      rw [show candidates = StableOccurrenceRanks.candidateKeys values by
        exact directSourceFinalOccurrenceCandidateKeys_eq_candidateKeys
          decider symbols]
    _ |>.Perm (StableOccurrenceRanks.candidateKeys values) :=
      StableOccurrenceRanks.map_cyclicSuccessorKey_perm_candidateKeys
        values (fun value _valueMember =>
          directSourceFinalAtomIdentityCodes_count_le_three
            decider symbols value)
    _ |>.Perm candidates := by
      rw [show candidates = StableOccurrenceRanks.candidateKeys values by
        exact directSourceFinalOccurrenceCandidateKeys_eq_candidateKeys
          decider symbols]
    _ |>.Perm current := currentCandidates.symm

end LeanTrominoes.PeriodicCNFStripReduction

end
