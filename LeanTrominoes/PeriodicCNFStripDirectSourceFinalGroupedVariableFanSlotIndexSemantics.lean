/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.KeyedAlignedDatumRange
import LeanTrominoes.ListAlignedMapLookup
import LeanTrominoes.ListZipWithProject
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedOccurrenceIndexSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedOccurrenceSlotSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableFanDataSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableFanSlotSemantics

/-! # Shared occurrence indices of grouped variable fan slots -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- Grouped variable-fan data are ordinary lookups at the same recovered
clause-major occurrence positions as the grouped occurrence records. -/
theorem directSourceFinalGroupedVariableFanData_eq_map_getD
    (symbols : List encoding.Γ) :
    directSourceFinalGroupedVariableFanData decider symbols =
      (directSourceFinalGroupedOccurrenceIndices decider symbols).map
        fun index =>
          (directSourceFinalVariableFanData decider symbols).getD
            index default := by
  let keys := directSourceFinalOccurrenceCandidateKeys decider symbols
  let queries := directSourceFinalUniqueFanQueryKeys decider symbols
  let fans := directSourceFinalVariableFanData decider symbols
  let indices := directSourceFinalOccurrenceCandidateIndices decider symbols
  apply List.eq_map_lookup_of_aligned_maps queries
    (directSourceFinalGroupedVariableFanData decider symbols)
    (directSourceFinalGroupedOccurrenceIndices decider symbols)
    (FiniteAlphabetKeyedValueLookup.alignedDatum keys fans)
    (UnaryKeyedValueLookup.alignedDatum keys indices)
    (fun index => fans.getD index default)
  · exact directSourceFinalGroupedVariableFanData_eq_map_alignedDatum
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
      keys fans query queryInKeys

/-- Grouped occurrence slots are lookups at those same clause-major
occurrence positions. -/
theorem directSourceFinalGroupedOccurrenceSlots_eq_map_getD
    (symbols : List encoding.Γ) :
    directSourceFinalGroupedOccurrenceSlots decider symbols =
      (directSourceFinalGroupedOccurrenceIndices decider symbols).map
        fun index =>
          (directSourceFinalOccurrenceSlots decider symbols).getD
            index default := by
  let keys := directSourceFinalOccurrenceCandidateKeys decider symbols
  let queries := directSourceFinalUniqueFanQueryKeys decider symbols
  let slots := directSourceFinalOccurrenceSlots decider symbols
  let indices := directSourceFinalOccurrenceCandidateIndices decider symbols
  apply List.eq_map_lookup_of_aligned_maps queries
    (directSourceFinalGroupedOccurrenceSlots decider symbols)
    (directSourceFinalGroupedOccurrenceIndices decider symbols)
    (FiniteAlphabetKeyedValueLookup.alignedDatum keys slots)
    (UnaryKeyedValueLookup.alignedDatum keys indices)
    (fun index => slots.getD index default)
  · exact directSourceFinalGroupedOccurrenceSlots_eq_map_alignedDatum
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
      keys slots query queryInKeys

/-- The complete grouped fan/slot column is selected pointwise by one shared
stable occurrence-index stream. -/
theorem directSourceFinalGroupedVariableFanSlots_eq_map_getD
    (symbols : List encoding.Γ) :
    directSourceFinalGroupedVariableFanSlots decider symbols =
      (directSourceFinalGroupedOccurrenceIndices decider symbols).map
        fun index =>
          ((directSourceFinalVariableFanData decider symbols).getD
              index default,
            groupedVariableFanGenericSlot
              ((directSourceFinalOccurrenceSlots decider symbols).getD
                index default)) := by
  rw [directSourceFinalGroupedVariableFanSlots_eq_zipWith,
    directSourceFinalGroupedVariableFanData_eq_map_getD,
    directSourceFinalGroupedOccurrenceSlots_eq_map_getD,
    List.zipWith_map_map_same]

end LeanTrominoes.PeriodicCNFStripReduction

end
