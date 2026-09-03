/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FinalFanDataStableProjection
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceSlotCompiler
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMVariableSiteDrawing
import LeanTrominoes.StableOccurrenceRankCyclicSuccessorPermutation

/-! # Connector kinds selected by stable occurrence keys -/

noncomputable section

namespace LeanTrominoes.FinalFanDataTripleAssembler

open PeriodicOneInThreeToThreeDM
open PeriodicPlanarOneInThreeToThreeDM

/-- At a genuine stable occurrence key, the semantic fan's corresponding
active slot selects exactly the record looked up by that key. -/
theorem stableFan_kind_of_candidateKey
    (values : List Nat) (records : List OccurrenceData)
    (countLe : ∀ value ∈ values, values.count value ≤ 3)
    (key : Nat) (keyMember : key ∈ StableOccurrenceRanks.candidateKeys values) :
    (stableFan (StableOccurrenceRanks.candidateKeys values) records
        (key / 3)
        (BoundedPositiveCountPreds.boundedPositiveCountPred
          (values.count (key / 3)))).kind
      (occurrenceVariableSiteSlot
        (BoundedOccurrenceSlots.boundedOccurrenceSlot (key % 3))) =
      (FiniteAlphabetKeyedValueLookup.alignedDatum
        (StableOccurrenceRanks.candidateKeys values) records key).kind := by
  rcases (StableOccurrenceRanks.mem_candidateKeys_iff values key).mp
      keyMember with
    ⟨value, rank, valueMember, rankLt, keyEq⟩
  have countLeValue : values.count value ≤ 3 :=
    countLe value valueMember
  have rankThree : rank < 3 := lt_of_lt_of_le rankLt countLeValue
  have positive : 0 < values.count value := by omega
  have countEq :=
    BoundedPositiveCountPreds.boundedPositiveCountPred_add_one_of_pos_le_three
      (values.count value) positive countLeValue
  have keyDiv : key / 3 = value := by omega
  have keyMod : key % 3 = rank := by omega
  have slotIndex :
      (occurrenceVariableSiteSlot
        (BoundedOccurrenceSlots.boundedOccurrenceSlot (key % 3))).index =
        rank := by
    rw [occurrenceVariableSiteSlot_index, keyMod]
    exact BoundedOccurrenceSlots.boundedOccurrenceSlot_index_of_lt_three
      rank rankThree
  rw [stableFan_kind_of_active]
  · congr 2
    omega
  · rw [slotIndex, keyDiv, countEq]
    exact rankLt

/-- At a genuine stable occurrence key, the semantic fan's corresponding
active slot selects exactly the polarity looked up by that key. -/
theorem stableFan_polarity_of_candidateKey
    (values : List Nat) (records : List OccurrenceData)
    (countLe : ∀ value ∈ values, values.count value ≤ 3)
    (key : Nat) (keyMember : key ∈ StableOccurrenceRanks.candidateKeys values) :
    (stableFan (StableOccurrenceRanks.candidateKeys values) records
        (key / 3)
        (BoundedPositiveCountPreds.boundedPositiveCountPred
          (values.count (key / 3)))).polarity
      (occurrenceVariableSiteSlot
        (BoundedOccurrenceSlots.boundedOccurrenceSlot (key % 3))) =
      (FiniteAlphabetKeyedValueLookup.alignedDatum
        (StableOccurrenceRanks.candidateKeys values) records key).polarity := by
  rcases (StableOccurrenceRanks.mem_candidateKeys_iff values key).mp
      keyMember with
    ⟨value, rank, valueMember, rankLt, keyEq⟩
  have countLeValue : values.count value ≤ 3 :=
    countLe value valueMember
  have rankThree : rank < 3 := lt_of_lt_of_le rankLt countLeValue
  have positive : 0 < values.count value := by omega
  have countEq :=
    BoundedPositiveCountPreds.boundedPositiveCountPred_add_one_of_pos_le_three
      (values.count value) positive countLeValue
  have keyDiv : key / 3 = value := by omega
  have keyMod : key % 3 = rank := by omega
  have slotIndex :
      (occurrenceVariableSiteSlot
        (BoundedOccurrenceSlots.boundedOccurrenceSlot (key % 3))).index =
        rank := by
    rw [occurrenceVariableSiteSlot_index, keyMod]
    exact BoundedOccurrenceSlots.boundedOccurrenceSlot_index_of_lt_three
      rank rankThree
  rw [stableFan_polarity_of_active]
  · congr 2
    omega
  · rw [slotIndex, keyDiv, countEq]
    exact rankLt

/-- At a genuine stable occurrence key, the semantic fan's corresponding
active slot selects exactly the direction looked up by that key. -/
theorem stableFan_direction_of_candidateKey
    (values : List Nat) (records : List OccurrenceData)
    (countLe : ∀ value ∈ values, values.count value ≤ 3)
    (key : Nat) (keyMember : key ∈ StableOccurrenceRanks.candidateKeys values) :
    (stableFan (StableOccurrenceRanks.candidateKeys values) records
        (key / 3)
        (BoundedPositiveCountPreds.boundedPositiveCountPred
          (values.count (key / 3)))).direction
      (occurrenceVariableSiteSlot
        (BoundedOccurrenceSlots.boundedOccurrenceSlot (key % 3))) =
      (FiniteAlphabetKeyedValueLookup.alignedDatum
        (StableOccurrenceRanks.candidateKeys values) records key).direction := by
  rcases (StableOccurrenceRanks.mem_candidateKeys_iff values key).mp
      keyMember with
    ⟨value, rank, valueMember, rankLt, keyEq⟩
  have countLeValue : values.count value ≤ 3 :=
    countLe value valueMember
  have rankThree : rank < 3 := lt_of_lt_of_le rankLt countLeValue
  have positive : 0 < values.count value := by omega
  have countEq :=
    BoundedPositiveCountPreds.boundedPositiveCountPred_add_one_of_pos_le_three
      (values.count value) positive countLeValue
  have keyDiv : key / 3 = value := by omega
  have keyMod : key % 3 = rank := by omega
  have slotIndex :
      (occurrenceVariableSiteSlot
        (BoundedOccurrenceSlots.boundedOccurrenceSlot (key % 3))).index =
        rank := by
    rw [occurrenceVariableSiteSlot_index, keyMod]
    exact BoundedOccurrenceSlots.boundedOccurrenceSlot_index_of_lt_three
      rank rankThree
  rw [stableFan_direction_of_active]
  · congr 2
    omega
  · rw [slotIndex, keyDiv, countEq]
    exact rankLt

end LeanTrominoes.FinalFanDataTripleAssembler

end
