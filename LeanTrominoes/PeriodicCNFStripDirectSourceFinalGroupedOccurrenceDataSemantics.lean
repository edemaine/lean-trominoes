/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteAlphabetKeyedValueLookupUniqueSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedOccurrenceDataCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceCandidateKeyNodup
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalUniqueFanQueryKeySemantics

/-! # Semantics of variable-major final occurrence records -/

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- The grouped stream recovers the unique occurrence record associated
with each distinct active fan key. -/
theorem directSourceFinalGroupedOccurrenceData_eq_map_alignedDatum
    (symbols : List encoding.Γ) :
    directSourceFinalGroupedOccurrenceData decider symbols =
      (directSourceFinalUniqueFanQueryKeys decider symbols).map
        (FiniteAlphabetKeyedValueLookup.alignedDatum
          (directSourceFinalOccurrenceCandidateKeys decider symbols)
          (directSourceFinalCompiledOccurrenceData decider symbols)) := by
  unfold directSourceFinalGroupedOccurrenceData
  apply FiniteAlphabetKeyedValueLookup.values_eq_map_alignedDatum
  · exact directSourceFinalOccurrenceCandidateKeys_length decider symbols
  · exact directSourceFinalOccurrenceCandidateKeys_nodup decider symbols
  · intro query queryMember
    exact directSourceFinalUniqueFanQueryKey_mem_candidateKeys
      decider symbols query queryMember

@[simp] theorem directSourceFinalGroupedOccurrenceData_length
    (symbols : List encoding.Γ) :
    (directSourceFinalGroupedOccurrenceData decider symbols).length =
      (directSourceFinalUniqueFanQueryKeys decider symbols).length := by
  rw [directSourceFinalGroupedOccurrenceData_eq_map_alignedDatum]
  simp

end LeanTrominoes.PeriodicCNFStripReduction
