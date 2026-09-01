/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteAlphabetKeyedValueLookupUniqueSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableFanDataCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceCandidateKeyNodup
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalUniqueFanQueryKeySemantics

/-! # Semantics of stable-identity final variable-fan records -/

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- The grouped stream recovers the unique complete variable-fan record
associated with each distinct active fan key. -/
theorem directSourceFinalGroupedVariableFanData_eq_map_alignedDatum
    (symbols : List encoding.Γ) :
    directSourceFinalGroupedVariableFanData decider symbols =
      (directSourceFinalUniqueFanQueryKeys decider symbols).map
        (FiniteAlphabetKeyedValueLookup.alignedDatum
          (directSourceFinalOccurrenceCandidateKeys decider symbols)
          (directSourceFinalVariableFanData decider symbols)) := by
  unfold directSourceFinalGroupedVariableFanData
  apply FiniteAlphabetKeyedValueLookup.values_eq_map_alignedDatum
  · rw [directSourceFinalOccurrenceCandidateKeys_length,
      directSourceFinalVariableFanData_length]
  · exact directSourceFinalOccurrenceCandidateKeys_nodup decider symbols
  · intro query queryMember
    exact directSourceFinalUniqueFanQueryKey_mem_candidateKeys
      decider symbols query queryMember

@[simp] theorem directSourceFinalGroupedVariableFanData_length
    (symbols : List encoding.Γ) :
    (directSourceFinalGroupedVariableFanData decider symbols).length =
      (directSourceFinalUniqueFanQueryKeys decider symbols).length := by
  rw [directSourceFinalGroupedVariableFanData_eq_map_alignedDatum]
  simp

end LeanTrominoes.PeriodicCNFStripReduction
