/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListRangeGetD
import LeanTrominoes.PeriodicCNFStripCountedContractedIncidenceBlockSemantics
import LeanTrominoes.PeriodicCNFStripCountedContractedIncidenceOccurrenceKeySemantics
import LeanTrominoes.StableOccurrenceRankCandidateKeyNodup

/-! # Ranked-index semantics shared by all counted incidence fields -/

namespace LeanTrominoes.PeriodicCNFStripReduction
namespace CountedContractedIncidence

/-- A valid degree block is the consecutive base-three rank interval for its
element code. -/
theorem queryBlock_eq_map_range
    (elementCode size : Nat) (valid : size = 2 ∨ size = 3) :
    queryBlock elementCode size =
      (List.range size).map fun rank => elementCode * 3 + rank := by
  rcases valid with rfl | rfl <;>
    norm_num [queryBlock, List.range_succ, Nat.mul_comm]

/-- Stable-key lookup of one valid element block recovers
exactly the presentation indices of that element's occurrences, preserving
their original order. -/
theorem queryBlock_map_candidateIndex_eq_idxsOf
    (incidenceElementCodes : List Nat)
    (countLeThree : ∀ code ∈ incidenceElementCodes,
      incidenceElementCodes.count code ≤ 3)
    (elementCode size : Nat)
    (valid : size = 2 ∨ size = 3)
    (sizeEq : size = incidenceElementCodes.count elementCode) :
    (queryBlock elementCode size).map
        ((StableOccurrenceRanks.candidateKeys incidenceElementCodes).idxOf) =
      incidenceElementCodes.idxsOf elementCode := by
  rw [queryBlock_eq_map_range elementCode size valid, List.map_map]
  have rangeLength :
      size = (incidenceElementCodes.idxsOf elementCode).length := by
    simpa using sizeEq
  rw [rangeLength]
  conv_rhs => rw [← List.map_range_getD (incidenceElementCodes.idxsOf elementCode) 0]
  apply List.map_congr_left
  intro rank rankMember
  dsimp only [Function.comp_apply]
  exact StableOccurrenceRanks.candidateKeys_idxOf_rank
    incidenceElementCodes countLeThree elementCode rank (by
      rw [← sizeEq, rangeLength]
      exact List.mem_range.mp rankMember)

/-- Mapping stable-key index lookup over the counted query stream groups
incidences by element code while preserving presentation order within each group. -/
theorem queryKeys_map_candidateIndex_eq_flatMap_idxsOf
    (elementCodes sizes incidenceElementCodes : List Nat)
    (columnsAligned : elementCodes.length = sizes.length)
    (degreesValid : ∀ size ∈ sizes, size = 2 ∨ size = 3)
    (countsAgree : ∀ pair ∈ elementCodes.zip sizes,
      pair.2 = incidenceElementCodes.count pair.1)
    (countLeThree : ∀ code ∈ incidenceElementCodes,
      incidenceElementCodes.count code ≤ 3) :
    (queryKeys elementCodes sizes).map
        ((StableOccurrenceRanks.candidateKeys incidenceElementCodes).idxOf) =
      elementCodes.flatMap fun elementCode =>
        incidenceElementCodes.idxsOf elementCode := by
  induction sizes generalizing elementCodes with
  | nil =>
      have codesNil : elementCodes = [] :=
        List.eq_nil_of_length_eq_zero (by simpa using columnsAligned)
      subst elementCodes
      rfl
  | cons size sizes induction =>
      cases elementCodes with
      | nil => simp at columnsAligned
      | cons elementCode elementCodes =>
          have tailAligned : elementCodes.length = sizes.length := by
            simpa using columnsAligned
          have headValid : size = 2 ∨ size = 3 :=
            degreesValid size (by simp)
          have tailValid : ∀ other ∈ sizes,
              other = 2 ∨ other = 3 := by
            intro other member
            exact degreesValid other (by simp [member])
          have headCount :
              size = incidenceElementCodes.count elementCode := by
            exact countsAgree (elementCode, size) (by simp)
          have tailCounts : ∀ pair ∈ elementCodes.zip sizes,
              pair.2 = incidenceElementCodes.count pair.1 := by
            intro pair member
            exact countsAgree pair (by simp [member])
          rw [show queryKeys (elementCode :: elementCodes)
                (size :: sizes) =
              queryBlock elementCode size ++
                queryKeys elementCodes sizes by
              rcases headValid with rfl | rfl
              · simp [queryBlock]
              · simp [queryBlock]]
          rw [List.map_append, List.flatMap_cons,
            queryBlock_map_candidateIndex_eq_idxsOf
              incidenceElementCodes countLeThree
              elementCode size headValid headCount,
            induction elementCodes tailAligned tailValid tailCounts]

/-- The degree-expansion permutation contract supplies all hypotheses needed
for the full stable lookup to become presentation-order grouping by raw
element code. -/
theorem queryKeys_map_candidateIndex_eq_flatMap_idxsOf_of_perm_expanded
    (elementCodes sizes incidenceElementCodes : List Nat)
    (columnsAligned : elementCodes.length = sizes.length)
    (degreesValid : ∀ size ∈ sizes, size = 2 ∨ size = 3)
    (elementCodesNodup : elementCodes.Nodup)
    (incidencePermutation : incidenceElementCodes.Perm
      (expandedElementCodes (elementCodes.zip sizes))) :
    (queryKeys elementCodes sizes).map
        ((StableOccurrenceRanks.candidateKeys incidenceElementCodes).idxOf) =
      elementCodes.flatMap fun elementCode =>
        incidenceElementCodes.idxsOf elementCode := by
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
  apply queryKeys_map_candidateIndex_eq_flatMap_idxsOf
    elementCodes sizes incidenceElementCodes
    columnsAligned degreesValid
  · intro pair pairMember
    exact (incidenceElementCodes_count_eq_degree_of_perm_expanded
      pairs incidenceElementCodes pairCodesNodup incidencePermutation
      pair pairMember).symm
  · exact incidenceElementCodes_count_le_three_of_perm_expanded
      pairs incidenceElementCodes pairCodesNodup pairDegreesValid
      incidencePermutation

end CountedContractedIncidence
end LeanTrominoes.PeriodicCNFStripReduction
