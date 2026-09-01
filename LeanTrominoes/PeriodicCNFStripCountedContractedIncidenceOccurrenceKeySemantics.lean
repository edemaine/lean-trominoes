/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripCountedContractedIncidenceSemantics
import LeanTrominoes.StableOccurrenceRankCandidateKeyNodup

/-! # Occurrence-key coverage for counted contraction -/

namespace LeanTrominoes.PeriodicCNFStripReduction
namespace CountedContractedIncidence

/-- Element codes repeated by their declared degrees. -/
def expandedElementCodes (pairs : List (Nat × Nat)) : List Nat :=
  pairs.flatMap fun pair => List.replicate pair.2 pair.1

/-- Requested base-three occurrence keys presented by explicit code/degree
pairs. -/
def pairQueryKeys (pairs : List (Nat × Nat)) : List Nat :=
  pairs.flatMap fun pair => queryBlock pair.1 pair.2

/-- The list-column query compiler is the explicit pairwise presentation. -/
theorem queryKeys_eq_pairQueryKeys
    (elementCodes sizes : List Nat)
    (aligned : elementCodes.length = sizes.length)
    (degreesValid : ∀ size ∈ sizes, size = 2 ∨ size = 3) :
    queryKeys elementCodes sizes =
      pairQueryKeys (elementCodes.zip sizes) := by
  induction sizes generalizing elementCodes with
  | nil =>
      have codesNil : elementCodes = [] :=
        List.eq_nil_of_length_eq_zero (by simpa using aligned)
      subst elementCodes
      rfl
  | cons size sizes induction =>
      cases elementCodes with
      | nil => simp at aligned
      | cons elementCode elementCodes =>
          have tailAligned : elementCodes.length = sizes.length := by
            simpa using aligned
          have headValid : size = 2 ∨ size = 3 :=
            degreesValid size (by simp)
          have tailValid : ∀ other ∈ sizes,
              other = 2 ∨ other = 3 := by
            intro other member
            exact degreesValid other (by simp [member])
          rcases headValid with rfl | rfl <;>
            simp [pairQueryKeys,
              induction elementCodes tailAligned tailValid, queryBlock]

private theorem not_mem_expandedElementCodes
    (pairs : List (Nat × Nat)) (value : Nat)
    (absent : value ∉ pairs.map Prod.fst) :
    value ∉ expandedElementCodes pairs := by
  induction pairs with
  | nil => simp [expandedElementCodes]
  | cons pair pairs induction =>
      have headDifferent : value ≠ pair.1 := by
        intro same
        apply absent
        simp [same]
      have tailAbsent : value ∉ pairs.map Prod.fst := by
        intro member
        exact absent (by simp [member])
      change value ∉
        List.replicate pair.2 pair.1 ++ expandedElementCodes pairs
      simp [headDifferent, induction tailAbsent]

/-- A duplicate-free element column makes each expanded code occur exactly
its declared number of times. -/
theorem expandedElementCodes_count_of_mem
    (pairs : List (Nat × Nat))
    (codesNodup : (pairs.map Prod.fst).Nodup)
    (pair : Nat × Nat) (pairMember : pair ∈ pairs) :
    (expandedElementCodes pairs).count pair.1 = pair.2 := by
  induction pairs with
  | nil => simp at pairMember
  | cons head pairs induction =>
      have nodupParts := List.nodup_cons.mp codesNodup
      simp only [List.mem_cons] at pairMember
      rcases pairMember with rfl | pairMember
      · change
          (List.replicate pair.2 pair.1 ++
            expandedElementCodes pairs).count pair.1 = pair.2
        rw [List.count_append,
          List.count_eq_zero.mpr
            (not_mem_expandedElementCodes pairs pair.1 nodupParts.1)]
        simp
      · have pairCodeMember : pair.1 ∈ pairs.map Prod.fst := by
          exact List.mem_map.mpr ⟨pair, pairMember, rfl⟩
        have different : head.1 ≠ pair.1 := by
          intro same
          apply nodupParts.1
          simpa [same] using pairCodeMember
        change
          (List.replicate head.2 head.1 ++
            expandedElementCodes pairs).count pair.1 = pair.2
        rw [List.count_append, induction nodupParts.2 pairMember]
        have countZero :
            (List.replicate head.2 head.1).count pair.1 = 0 :=
          List.count_eq_zero.mpr (fun member =>
            (Ne.symm different) (List.eq_of_mem_replicate member))
        rw [countZero, Nat.zero_add]

private theorem expandedElementCodes_count_le_three
    (pairs : List (Nat × Nat))
    (codesNodup : (pairs.map Prod.fst).Nodup)
    (degreesValid : ∀ pair ∈ pairs, pair.2 = 2 ∨ pair.2 = 3)
    (value : Nat) (valueMember : value ∈ expandedElementCodes pairs) :
    (expandedElementCodes pairs).count value ≤ 3 := by
  unfold expandedElementCodes at valueMember
  simp only [List.mem_flatMap] at valueMember
  obtain ⟨pair, pairMember, valueMember⟩ := valueMember
  have valueEq : value = pair.1 := List.eq_of_mem_replicate valueMember
  subst value
  rw [expandedElementCodes_count_of_mem pairs codesNodup pair pairMember]
  rcases degreesValid pair pairMember with degreeEq | degreeEq <;>
    omega

private theorem queryBlock_rank
    (elementCode size query : Nat)
    (valid : size = 2 ∨ size = 3)
    (queryMember : query ∈ queryBlock elementCode size) :
    ∃ rank, rank < size ∧ query = elementCode * 3 + rank := by
  rcases valid with rfl | rfl <;>
    simp [queryBlock, Nat.mul_comm] at queryMember <;>
    rcases queryMember with rfl | rfl | rfl <;>
    first
    | exact ⟨0, by omega, by omega⟩
    | exact ⟨1, by omega, by omega⟩
    | exact ⟨2, by omega, by omega⟩

/-- If incidence codes are a permutation of the degree expansion, their
stable occurrence keys are unique. -/
theorem incidenceBlockKeys_nodup_of_perm_expanded
    (pairs : List (Nat × Nat)) (incidenceElementCodes : List Nat)
    (codesNodup : (pairs.map Prod.fst).Nodup)
    (degreesValid : ∀ pair ∈ pairs, pair.2 = 2 ∨ pair.2 = 3)
    (incidencePermutation :
      incidenceElementCodes.Perm (expandedElementCodes pairs)) :
    (incidenceBlockKeys incidenceElementCodes).Nodup := by
  rw [incidenceBlockKeys_eq_candidateKeys]
  apply StableOccurrenceRanks.candidateKeys_nodup_of_count_le_three
  intro value valueMember
  have expandedMember : value ∈ expandedElementCodes pairs :=
    incidencePermutation.mem_iff.mp valueMember
  rw [incidencePermutation.count_eq value]
  exact expandedElementCodes_count_le_three
    pairs codesNodup degreesValid value expandedMember

/-- Under the same degree-expansion contract, every requested element/rank
key occurs in the stable incidence candidate column. -/
theorem pairQueryKeys_present_of_perm_expanded
    (pairs : List (Nat × Nat)) (incidenceElementCodes : List Nat)
    (codesNodup : (pairs.map Prod.fst).Nodup)
    (degreesValid : ∀ pair ∈ pairs, pair.2 = 2 ∨ pair.2 = 3)
    (incidencePermutation :
      incidenceElementCodes.Perm (expandedElementCodes pairs)) :
    ∀ query ∈ pairQueryKeys pairs,
      query ∈ incidenceBlockKeys incidenceElementCodes := by
  intro query queryMember
  unfold pairQueryKeys at queryMember
  simp only [List.mem_flatMap] at queryMember
  obtain ⟨pair, pairMember, queryMember⟩ := queryMember
  obtain ⟨rank, rankLt, queryEq⟩ := queryBlock_rank
    pair.1 pair.2 query (degreesValid pair pairMember) queryMember
  rw [incidenceBlockKeys_eq_candidateKeys, queryEq]
  apply StableOccurrenceRanks.candidateKey_mem_of_rank_lt_count
  rw [incidencePermutation.count_eq pair.1,
    expandedElementCodes_count_of_mem pairs codesNodup pair pairMember]
  exact rankLt

/-- Aligned valid code/degree columns inherit unique covering occurrence keys
from a duplicate-free element column and an incidence permutation of its
degree expansion. -/
theorem occurrenceKeyContract_of_perm_expanded
    (elementCodes sizes incidenceElementCodes : List Nat)
    (aligned : elementCodes.length = sizes.length)
    (degreesValid : ∀ size ∈ sizes, size = 2 ∨ size = 3)
    (elementCodesNodup : elementCodes.Nodup)
    (incidencePermutation : incidenceElementCodes.Perm
      (expandedElementCodes (elementCodes.zip sizes))) :
    (incidenceBlockKeys incidenceElementCodes).Nodup ∧
      ∀ query ∈ queryKeys elementCodes sizes,
        query ∈ incidenceBlockKeys incidenceElementCodes := by
  let pairs := elementCodes.zip sizes
  have pairCodes : pairs.map Prod.fst = elementCodes := by
    exact List.map_fst_zip (by omega)
  have pairSizes : pairs.map Prod.snd = sizes := by
    exact List.map_snd_zip (by omega)
  have pairCodesNodup : (pairs.map Prod.fst).Nodup := by
    rw [pairCodes]
    exact elementCodesNodup
  have pairDegreesValid : ∀ pair ∈ pairs,
      pair.2 = 2 ∨ pair.2 = 3 := by
    intro pair pairMember
    apply degreesValid pair.2
    rw [← pairSizes]
    exact List.mem_map.mpr ⟨pair, pairMember, rfl⟩
  constructor
  · exact incidenceBlockKeys_nodup_of_perm_expanded
      pairs incidenceElementCodes pairCodesNodup pairDegreesValid
      incidencePermutation
  · intro query queryMember
    rw [queryKeys_eq_pairQueryKeys
      elementCodes sizes aligned degreesValid] at queryMember
    exact pairQueryKeys_present_of_perm_expanded
      pairs incidenceElementCodes pairCodesNodup pairDegreesValid
      incidencePermutation query queryMember

end CountedContractedIncidence
end LeanTrominoes.PeriodicCNFStripReduction
