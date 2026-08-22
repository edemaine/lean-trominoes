/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GroupedListIndex
import LeanTrominoes.LastOccurrenceBlockStarts
import LeanTrominoes.PeriodicCNFSourceOccurrenceAtomRankSemantics
import LeanTrominoes.PeriodicThreeSATThreeExactFormulaVariableEnumeration
import LeanTrominoes.PeriodicThreeSATThreeExactSize
import LeanTrominoes.PeriodicThreeSATThreeOccurrenceLocalIndex
import LeanTrominoes.RotatedListIndex

/-! # Exact target indices of copied source occurrences -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

private theorem tail_append_take_one_length {Value : Type*}
    (values : List Value) :
    (values.tail ++ values.take 1).length = values.length := by
  cases values <;> simp

/-- The grouped-and-rotated variable index of a positional source copy is
its last-occurrence-ordered atom-block start plus its rotated local rank. -/
theorem occurrence_rotatedOccurrenceVariables_idxOf_decidableEq
    (source : PeriodicCNF Nat)
    (tagged : ThreeOccurrenceVariable Nat × Nat)
    (taggedMember : tagged ∈ (allOccurrenceVariables source).zipIdx) :
    @List.idxOf (ThreeOccurrenceVariable Nat)
        instBEqOfDecidableEq tagged.1
        (rotatedOccurrenceVariables source) =
      LastOccurrenceBlockStarts.blockStart
          (PeriodicCNF.SourceOccurrenceAtomRanks.occurrenceAtoms source)
          tagged.1.1 +
        UnaryRotatedRanksMachine.rotatedRank
          (((PeriodicCNF.SourceOccurrenceAtomRanks.occurrenceAtoms
            source).take tagged.2).count tagged.1.1)
          ((PeriodicCNF.SourceOccurrenceAtomRanks.occurrenceAtoms
            source).count tagged.1.1) := by
  let atoms :=
    PeriodicCNF.SourceOccurrenceAtomRanks.occurrenceAtoms source
  let keys := sourceVariables source
  let block := fun atom : Nat =>
    (occurrenceVariables source atom).tail ++
      (occurrenceVariables source atom).take 1
  have atomsEq : atoms =
      (allOccurrenceVariables source).map Prod.fst := by
    exact PeriodicCNF.SourceOccurrenceAtomRanks.occurrenceAtoms_eq_allOccurrenceVariables_fst
      source
  have copyMember : tagged.1 ∈ allOccurrenceVariables source :=
    List.fst_mem_of_mem_zipIdx taggedMember
  have atomMemAtoms : tagged.1.1 ∈ atoms := by
    rw [atomsEq]
    exact List.mem_map.mpr ⟨tagged.1, copyMember, rfl⟩
  have keysEq : keys = atoms.dedup := by
    rfl
  have atomMemKeys : tagged.1.1 ∈ keys := by
    rw [keysEq, List.mem_dedup]
    exact atomMemAtoms
  have copyMemBlock : tagged.1 ∈ occurrenceVariables source tagged.1.1 := by
    rw [occurrenceVariables_eq_filter]
    simp [copyMember]
  have copyMemRotatedBlock : tagged.1 ∈ block tagged.1.1 := by
    unfold block
    cases copiesEq : occurrenceVariables source tagged.1.1 with
    | nil => simp [copiesEq] at copyMemBlock
    | cons first rest =>
        by_cases copyFirst : tagged.1 = first
        · subst first
          simp
        · have copyRest : tagged.1 ∈ rest := by
            simpa [copiesEq, copyFirst] using copyMemBlock
          simp [copyRest]
  have blocksHaveKey : ∀ atom copy, copy ∈ block atom → copy.1 = atom := by
    intro atom copy copyInBlock
    unfold block at copyInBlock
    rcases List.mem_append.mp copyInBlock with copyInTail | copyInTake
    · exact occurrenceVariables_fst source atom
        (List.mem_of_mem_tail copyInTail)
    · exact occurrenceVariables_fst source atom
        (List.mem_of_mem_take copyInTake)
  have grouped :=
    GroupedListIndex.idxOf_flatMap_eq_prefix_sum_add_local
      keys block Prod.fst tagged.1.1 tagged.1 blocksHaveKey rfl
      atomMemKeys copyMemRotatedBlock
  have localRotated := RotatedListIndex.idxOf_tail_append_take_one
    (occurrenceVariables source tagged.1.1)
    (occurrenceVariables_nodup source tagged.1.1)
    tagged.1 copyMemBlock
  have localIndex :=
    occurrenceVariables_idxOf_eq_priorAtomCount source tagged taggedMember
  have blockLength :
      (occurrenceVariables source tagged.1.1).length =
        atoms.count tagged.1.1 := by
    simpa [atoms, PeriodicCNF.SourceOccurrenceAtomRanks.occurrenceAtoms]
      using occurrenceVariables_length_eq_count source tagged.1.1
  have localEq :
      @List.idxOf (ThreeOccurrenceVariable Nat)
          instBEqOfDecidableEq tagged.1 (block tagged.1.1) =
        UnaryRotatedRanksMachine.rotatedRank
          (((atoms.take tagged.2).count tagged.1.1))
          (atoms.count tagged.1.1) := by
    rw [show block tagged.1.1 =
        (occurrenceVariables source tagged.1.1).tail ++
          (occurrenceVariables source tagged.1.1).take 1 by rfl]
    rw [localRotated, localIndex]
    rw [blockLength, List.map_take, ← atomsEq]
  have prefixEq :
      (((keys.take (@List.idxOf Nat instBEqOfDecidableEq
          tagged.1.1 keys)).map fun atom => (block atom).length).sum) =
        LastOccurrenceBlockStarts.blockStart atoms tagged.1.1 := by
    rw [keysEq]
    unfold LastOccurrenceBlockStarts.blockStart
      LastOccurrenceBlockStarts.blockStartAux
    simp only [Nat.zero_add]
    apply congrArg List.sum
    apply List.map_congr_left
    intro atom atomMember
    rw [show (block atom).length =
        (occurrenceVariables source atom).length by
          exact tail_append_take_one_length _]
    simpa [atoms, PeriodicCNF.SourceOccurrenceAtomRanks.occurrenceAtoms]
      using occurrenceVariables_length_eq_count source atom
  rw [show rotatedOccurrenceVariables source = keys.flatMap block by rfl]
  rw [grouped, prefixEq, localEq]

end PeriodicThreeSATThree
end LeanTrominoes
