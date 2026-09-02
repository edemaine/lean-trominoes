/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.KeyedAlignedDatumRange
import LeanTrominoes.ListAlignedMapLookup
import LeanTrominoes.ListZipWithProject
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedOccurrenceDataSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedParentIndexPermutation

/-! # Joint regrouping of occurrences and parent indices -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- Grouped finite occurrence records are ordinary lookups at the same
grouped clause-major positions used by the parent-index compiler. -/
theorem directSourceFinalGroupedOccurrenceData_eq_map_getD
    (symbols : List encoding.Γ) :
    directSourceFinalGroupedOccurrenceData decider symbols =
      (directSourceFinalGroupedOccurrenceIndices decider symbols).map
        fun index =>
          (directSourceFinalCompiledOccurrenceData
            decider symbols).getD index default := by
  let keys := directSourceFinalOccurrenceCandidateKeys decider symbols
  let queries := directSourceFinalUniqueFanQueryKeys decider symbols
  let occurrences := directSourceFinalCompiledOccurrenceData decider symbols
  let indices := directSourceFinalOccurrenceCandidateIndices decider symbols
  apply List.eq_map_lookup_of_aligned_maps queries
    (directSourceFinalGroupedOccurrenceData decider symbols)
    (directSourceFinalGroupedOccurrenceIndices decider symbols)
    (FiniteAlphabetKeyedValueLookup.alignedDatum keys occurrences)
    (UnaryKeyedValueLookup.alignedDatum keys indices)
    (fun index => occurrences.getD index default)
  · exact directSourceFinalGroupedOccurrenceData_eq_map_alignedDatum
      decider symbols
  · exact directSourceFinalGroupedOccurrenceIndices_eq_map_alignedDatum
      decider symbols
  · intro query queryMember
    have queryInKeys : query ∈
        directSourceFinalOccurrenceCandidateKeys decider symbols :=
      directSourceFinalUniqueFanQueryKey_mem_candidateKeys
        decider symbols query queryMember
    unfold indices directSourceFinalOccurrenceCandidateIndices
      UnaryFieldRange.values
    exact FiniteAlphabetKeyedValueLookup.alignedDatum_eq_rangeIndex
      keys occurrences query queryInKeys

/-- The complete grouped `(occurrence, parent)` column is indexed by the
single shared grouped occurrence-position permutation. -/
theorem directSourceFinalGroupedOccurrenceParents_eq_map
    (symbols : List encoding.Γ) :
    List.zipWith Prod.mk
        (directSourceFinalGroupedOccurrenceData decider symbols)
        (directSourceFinalGroupedParentIndices decider symbols) =
      (directSourceFinalGroupedOccurrenceIndices decider symbols).map
        fun index =>
          ((directSourceFinalCompiledOccurrenceData
              decider symbols).getD index default,
            (directSourceFinalOccurrenceParentIndices
              decider symbols).getD index 0) := by
  rw [directSourceFinalGroupedOccurrenceData_eq_map_getD,
    directSourceFinalGroupedParentIndices_eq_map_getD,
    List.zipWith_map_map_same]

/-- Stable-key regrouping preserves occurrence data and its parent index
together, not merely as two independent permutations. -/
theorem directSourceFinalGroupedOccurrenceParents_perm
    (symbols : List encoding.Γ) :
    (List.zipWith Prod.mk
      (directSourceFinalGroupedOccurrenceData decider symbols)
      (directSourceFinalGroupedParentIndices decider symbols)).Perm
    (List.zipWith Prod.mk
      (directSourceFinalCompiledOccurrenceData decider symbols)
      (directSourceFinalOccurrenceParentIndices decider symbols)) := by
  rw [directSourceFinalGroupedOccurrenceParents_eq_map]
  let occurrences := directSourceFinalCompiledOccurrenceData decider symbols
  let parents := directSourceFinalOccurrenceParentIndices decider symbols
  let attach := fun index =>
    (occurrences.getD index default, parents.getD index 0)
  apply ((directSourceFinalGroupedOccurrenceIndices_perm_range
    decider symbols).map attach).trans
  change ((List.range occurrences.length).map attach).Perm _
  have parentLength : parents.length = occurrences.length :=
    directSourceFinalOccurrenceParentIndices_length decider symbols
  rw [← List.zipWith_map_map_same Prod.mk
    (fun index => occurrences.getD index default)
    (fun index => parents.getD index 0)]
  rw [List.map_range_getD occurrences default]
  rw [show List.range occurrences.length = List.range parents.length by
    rw [parentLength]]
  rw [List.map_range_getD parents 0]

end LeanTrominoes.PeriodicCNFStripReduction

end
