/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListRangeGetD
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedParentIndexSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalUniqueFanQueryKeyPermutation
import LeanTrominoes.UnaryIndexedValueLookupSemantics

/-! # Permutation semantics of grouped parent indices -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- The grouped occurrence positions are a permutation of the complete
clause-major occurrence-index range. -/
theorem directSourceFinalGroupedOccurrenceIndices_perm_range
    (symbols : List encoding.Γ) :
    (directSourceFinalGroupedOccurrenceIndices decider symbols).Perm
      (List.range
        (directSourceFinalCompiledOccurrenceData decider symbols).length) := by
  let keys := directSourceFinalOccurrenceCandidateKeys decider symbols
  let queries := directSourceFinalUniqueFanQueryKeys decider symbols
  let indices := directSourceFinalOccurrenceCandidateIndices decider symbols
  let datum := UnaryKeyedValueLookup.alignedDatum keys indices
  have aligned : keys.length = indices.length := by
    simp [keys, indices, directSourceFinalOccurrenceCandidateIndices,
      UnaryFieldRange.values]
  have keysNodup : keys.Nodup :=
    directSourceFinalOccurrenceCandidateKeys_nodup decider symbols
  have indicesEq : indices = keys.map datum :=
    UnaryKeyedValueLookup.candidateValues_eq_map_alignedDatum
      keys indices aligned keysNodup
  rw [directSourceFinalGroupedOccurrenceIndices_eq_map_alignedDatum]
  change (queries.map datum).Perm _
  calc
    (queries.map datum).Perm (keys.map datum) :=
      (directSourceFinalUniqueFanQueryKeys_perm_candidateKeys
        decider symbols).map datum
    _ = indices := indicesEq.symm
    _ = List.range
        (directSourceFinalCompiledOccurrenceData decider symbols).length := by
      unfold indices directSourceFinalOccurrenceCandidateIndices
        UnaryFieldRange.values
      rw [directSourceFinalOccurrenceCandidateKeys_length]

/-- In-range unary indexed lookup is ordinary total lookup at every grouped
occurrence position. -/
theorem directSourceFinalGroupedParentIndices_eq_map_getD
    (symbols : List encoding.Γ) :
    directSourceFinalGroupedParentIndices decider symbols =
      (directSourceFinalGroupedOccurrenceIndices decider symbols).map
        fun index =>
          (directSourceFinalOccurrenceParentIndices
            decider symbols).getD index 0 := by
  unfold directSourceFinalGroupedParentIndices
  apply UnaryIndexedValueLookup.values_eq_map_getD_of_forall_lt
  intro index indexMember
  rw [directSourceFinalOccurrenceParentIndices_length]
  exact directSourceFinalGroupedOccurrenceIndex_lt
    decider symbols index indexMember

/-- Regrouping by stable occurrence key loses or duplicates no parent-clause
index. -/
theorem directSourceFinalGroupedParentIndices_perm_occurrenceParents
    (symbols : List encoding.Γ) :
    (directSourceFinalGroupedParentIndices decider symbols).Perm
      (directSourceFinalOccurrenceParentIndices decider symbols) := by
  rw [directSourceFinalGroupedParentIndices_eq_map_getD]
  let parents := directSourceFinalOccurrenceParentIndices decider symbols
  have indicesPerm :=
    directSourceFinalGroupedOccurrenceIndices_perm_range decider symbols
  rw [← directSourceFinalOccurrenceParentIndices_length] at indicesPerm
  change ((directSourceFinalGroupedOccurrenceIndices decider symbols).map
      (fun index => parents.getD index 0)).Perm parents
  apply (indicesPerm.map fun index => parents.getD index 0).trans
  rw [List.map_range_getD]

end LeanTrominoes.PeriodicCNFStripReduction

end
