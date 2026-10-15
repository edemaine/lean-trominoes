/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SAT.CNF.Compiler.PeriodicCNFProgramSource
import LeanTrominoes.Complexity.FiniteAlphabetKeyedValueLookupUniqueSemantics
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Grouped.PeriodicCNFStripDirectSourceFinalGroupedOccurrenceSlotCompiler
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Occurrence.PeriodicCNFStripDirectSourceFinalOccurrenceCandidateKeyNodup
import LeanTrominoes.Tiling.Tromino.Strip.Direct.Source.Final.Unique.PeriodicCNFStripDirectSourceFinalUniqueFanQueryKeySemantics

/-! # Semantics of variable-major final occurrence slots -/

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.LeanTrominoes.FiniteEncoding Input}
variable {language : Input → Prop}
variable (decider : PeriodicCNF.ProgramSource encoding language)

/-- The grouped stream recovers the unique occurrence slot associated with
each distinct active fan key. -/
theorem directSourceFinalGroupedOccurrenceSlots_eq_map_alignedDatum
    (symbols : List encoding.Γ) :
    directSourceFinalGroupedOccurrenceSlots decider symbols =
      (directSourceFinalUniqueFanQueryKeys decider symbols).map
        (FiniteAlphabetKeyedValueLookup.alignedDatum
          (directSourceFinalOccurrenceCandidateKeys decider symbols)
          (directSourceFinalOccurrenceSlots decider symbols)) := by
  unfold directSourceFinalGroupedOccurrenceSlots
  apply FiniteAlphabetKeyedValueLookup.values_eq_map_alignedDatum
  · rw [directSourceFinalOccurrenceCandidateKeys_length,
      directSourceFinalOccurrenceSlots_length]
  · exact directSourceFinalOccurrenceCandidateKeys_nodup decider symbols
  · intro query queryMember
    exact directSourceFinalUniqueFanQueryKey_mem_candidateKeys
      decider symbols query queryMember

@[simp] theorem directSourceFinalGroupedOccurrenceSlots_length
    (symbols : List encoding.Γ) :
    (directSourceFinalGroupedOccurrenceSlots decider symbols).length =
      (directSourceFinalUniqueFanQueryKeys decider symbols).length := by
  rw [directSourceFinalGroupedOccurrenceSlots_eq_map_alignedDatum]
  simp

end LeanTrominoes.PeriodicCNFStripReduction
