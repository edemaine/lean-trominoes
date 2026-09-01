/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import Mathlib.Tactic.IntervalCases
import LeanTrominoes.StableOccurrenceRankCandidateKeyNodup

/-! # Cyclic permutation of stable occurrence keys -/

namespace LeanTrominoes.StableOccurrenceRanks

/-- Advance a base-three occurrence key cyclically within the multiplicity
of its identity. -/
def cyclicSuccessorKey (values : List Nat) (key : Nat) : Nat :=
  let value := key / 3
  value * 3 + ((key % 3 + 1) % values.count value)

/-- Candidate-key membership is equivalent to a genuine identity and a
rank below that identity's multiplicity. -/
theorem mem_candidateKeys_iff (values : List Nat) (key : Nat) :
    key ∈ candidateKeys values ↔
      ∃ value rank, value ∈ values ∧ rank < values.count value ∧
        key = value * 3 + rank := by
  constructor
  · intro keyMember
    rcases List.mem_iff_getElem.mp keyMember with
      ⟨index, indexLt, keyEq⟩
    have valueIndexLt : index < values.length := by
      simpa using indexLt
    let value := values[index]
    let rank := (ranks values)[index]'(by simpa using valueIndexLt)
    have rankEq : rank = (values.take index).count value := by
      have lookup := ranks_getElem? values index
      have rankIndexLt : index < (ranks values).length := by
        simpa using valueIndexLt
      simpa only [rank, value,
        List.getElem?_eq_getElem rankIndexLt,
        List.getElem?_eq_getElem valueIndexLt,
        Option.map_some, Option.some.injEq] using lookup
    have rankLt : rank < values.count value := by
      rw [rankEq]
      exact @List.count_getElem_take_lt_count Nat _ (by infer_instance)
        values index valueIndexLt
    refine ⟨value, rank, List.getElem_mem valueIndexLt, rankLt, ?_⟩
    rw [← keyEq]
    simp [candidateKeys, value, rank]
  · rintro ⟨value, rank, _valueMember, rankLt, rfl⟩
    exact candidateKey_mem_of_rank_lt_count values value rank rankLt

private theorem successorRank_injective
    (count first second : Nat)
    (positive : 0 < count) (atMostThree : count ≤ 3)
    (firstLt : first < count) (secondLt : second < count)
    (equal : (first + 1) % count = (second + 1) % count) :
    first = second := by
  interval_cases count <;> interval_cases first <;>
    interval_cases second <;> simp_all

private theorem cyclicSuccessorKey_injective_on
    (values : List Nat)
    (countLe : ∀ value ∈ values, values.count value ≤ 3)
    {first second : Nat}
    (firstMember : first ∈ candidateKeys values)
    (secondMember : second ∈ candidateKeys values)
    (equal : cyclicSuccessorKey values first =
      cyclicSuccessorKey values second) :
    first = second := by
  rcases (mem_candidateKeys_iff values first).mp firstMember with
    ⟨firstValue, firstRank, firstValueMember, firstRankLt, firstEq⟩
  rcases (mem_candidateKeys_iff values second).mp secondMember with
    ⟨secondValue, secondRank, secondValueMember, secondRankLt, secondEq⟩
  have firstCountLe := countLe firstValue firstValueMember
  have secondCountLe := countLe secondValue secondValueMember
  have firstRankThree : firstRank < 3 :=
    lt_of_lt_of_le firstRankLt firstCountLe
  have secondRankThree : secondRank < 3 :=
    lt_of_lt_of_le secondRankLt secondCountLe
  have firstDiv : (firstValue * 3 + firstRank) / 3 = firstValue := by
    omega
  have secondDiv : (secondValue * 3 + secondRank) / 3 = secondValue := by
    omega
  have firstMod : (firstValue * 3 + firstRank) % 3 = firstRank := by
    omega
  have secondMod : (secondValue * 3 + secondRank) % 3 = secondRank := by
    omega
  have firstPositive : 0 < values.count firstValue := by omega
  have secondPositive : 0 < values.count secondValue := by omega
  have firstNextLt :
      (firstRank + 1) % values.count firstValue < 3 :=
    lt_of_lt_of_le (Nat.mod_lt _ firstPositive) firstCountLe
  have secondNextLt :
      (secondRank + 1) % values.count secondValue < 3 :=
    lt_of_lt_of_le (Nat.mod_lt _ secondPositive) secondCountLe
  simp only [cyclicSuccessorKey, firstEq, secondEq, firstDiv, secondDiv,
    firstMod, secondMod] at equal
  have valueEq : firstValue = secondValue := by omega
  subst secondValue
  have rankEq : firstRank = secondRank :=
    successorRank_injective
      (values.count firstValue) firstRank secondRank
      firstPositive firstCountLe firstRankLt secondRankLt (by omega)
  omega

private theorem exists_cyclic_predecessor
    (count rank : Nat) (positive : 0 < count)
    (atMostThree : count ≤ 3) (rankLt : rank < count) :
    ∃ predecessor, predecessor < count ∧
      (predecessor + 1) % count = rank := by
  interval_cases count
  · have rankEq : rank = 0 := by omega
    subst rank
    exact ⟨0, by decide, by decide⟩
  · interval_cases rank
    · exact ⟨1, by decide, by decide⟩
    · exact ⟨0, by decide, by decide⟩
  · interval_cases rank
    · exact ⟨2, by decide, by decide⟩
    · exact ⟨0, by decide, by decide⟩
    · exact ⟨1, by decide, by decide⟩

/-- Advancing every stable base-three key to its cyclic successor only
permutes the complete occurrence-key column. -/
theorem map_cyclicSuccessorKey_perm_candidateKeys
    (values : List Nat)
    (countLe : ∀ value ∈ values, values.count value ≤ 3) :
    ((candidateKeys values).map (cyclicSuccessorKey values)).Perm
      (candidateKeys values) := by
  have keysNodup : (candidateKeys values).Nodup :=
    candidateKeys_nodup_of_count_le_three values countLe
  have mappedNodup :
      ((candidateKeys values).map (cyclicSuccessorKey values)).Nodup := by
    apply keysNodup.map_on
    intro first firstMember second secondMember equal
    exact cyclicSuccessorKey_injective_on values countLe
      firstMember secondMember equal
  apply List.perm_of_nodup_nodup_toFinset_eq mappedNodup keysNodup
  apply Finset.ext
  intro key
  simp only [List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨current, currentMember, rfl⟩
    rcases (mem_candidateKeys_iff values current).mp currentMember with
      ⟨value, rank, valueMember, rankLt, currentEq⟩
    have countLeThree := countLe value valueMember
    have rankThree : rank < 3 := lt_of_lt_of_le rankLt countLeThree
    have divEq : (value * 3 + rank) / 3 = value := by omega
    have modEq : (value * 3 + rank) % 3 = rank := by omega
    rw [cyclicSuccessorKey, currentEq, divEq, modEq]
    apply candidateKey_mem_of_rank_lt_count
    exact Nat.mod_lt _ (by omega)
  · intro keyMember
    rcases (mem_candidateKeys_iff values key).mp keyMember with
      ⟨value, rank, valueMember, rankLt, keyEq⟩
    have countLeThree := countLe value valueMember
    rcases exists_cyclic_predecessor
        (values.count value) rank (by omega) countLeThree rankLt with
      ⟨predecessor, predecessorLt, successorEq⟩
    let current := value * 3 + predecessor
    have predecessorThree : predecessor < 3 :=
      lt_of_lt_of_le predecessorLt countLeThree
    have divEq : current / 3 = value := by
      unfold current
      omega
    have modEq : current % 3 = predecessor := by
      unfold current
      omega
    refine ⟨current,
      candidateKey_mem_of_rank_lt_count values value predecessor
        predecessorLt, ?_⟩
    rw [cyclicSuccessorKey, divEq, modEq, successorEq, keyEq]

end LeanTrominoes.StableOccurrenceRanks
