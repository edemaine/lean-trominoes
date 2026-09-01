/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedOccurrenceIndexCompiler
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalOccurrenceCandidateKeyNodup
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalUniqueFanQueryKeySemantics
import LeanTrominoes.UnaryKeyedValueLookupUniqueSemantics

/-! # Semantics of variable-major final occurrence indices -/

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- Each distinct active key recovers its unique clause-major occurrence
position. -/
theorem directSourceFinalGroupedOccurrenceIndices_eq_map_alignedDatum
    (symbols : List encoding.Γ) :
    directSourceFinalGroupedOccurrenceIndices decider symbols =
      (directSourceFinalUniqueFanQueryKeys decider symbols).map
        (UnaryKeyedValueLookup.alignedDatum
          (directSourceFinalOccurrenceCandidateKeys decider symbols)
          (directSourceFinalOccurrenceCandidateIndices decider symbols)) := by
  unfold directSourceFinalGroupedOccurrenceIndices
  apply UnaryKeyedValueLookup.values_eq_map_alignedDatum
  · simp [directSourceFinalOccurrenceCandidateIndices,
      UnaryFieldRange.values]
  · exact directSourceFinalOccurrenceCandidateKeys_nodup decider symbols
  · intro query queryMember
    exact directSourceFinalUniqueFanQueryKey_mem_candidateKeys
      decider symbols query queryMember

@[simp] theorem directSourceFinalGroupedOccurrenceIndices_length
    (symbols : List encoding.Γ) :
    (directSourceFinalGroupedOccurrenceIndices decider symbols).length =
      (directSourceFinalUniqueFanQueryKeys decider symbols).length := by
  rw [directSourceFinalGroupedOccurrenceIndices_eq_map_alignedDatum]
  simp

end LeanTrominoes.PeriodicCNFStripReduction
