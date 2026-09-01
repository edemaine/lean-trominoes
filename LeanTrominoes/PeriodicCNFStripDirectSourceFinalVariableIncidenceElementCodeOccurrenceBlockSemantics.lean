/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListZipWithFourFlatMapSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalVariableIncidenceBaseBroadcastSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalVariableIncidenceElementCodeBlockSemantics

/-! # Occurrence blocks of final variable-incidence element codes -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- The full compiled variable-incidence code stream is the flattening of
one explicit finite selector block for every grouped occurrence, supplied
with its current key, cyclic-successor key, and parent clause index. -/
theorem directSourceFinalVariableIncidenceElementCodes_eq_occurrenceBlocks
    (symbols : List encoding.Γ) :
    directSourceFinalVariableIncidenceElementCodes decider symbols =
      (List.zipWith4 groupedVariableIncidenceElementCodeBlock
        (directSourceFinalGroupedVariableFanSlots decider symbols)
        (directSourceFinalUniqueFanQueryKeys decider symbols)
        (directSourceFinalGroupedNextOccurrenceKeys decider symbols)
        (directSourceFinalGroupedParentIndices decider symbols)).flatten := by
  rw [directSourceFinalVariableIncidenceElementCodes_eq_zipWith4,
    directSourceFinalVariableIncidenceCurrentKeys_eq_broadcastValues,
    directSourceFinalVariableIncidenceNextKeys_eq_broadcastValues,
    directSourceFinalVariableIncidenceParentIndices_eq_broadcastValues]
  unfold directSourceFinalVariableIncidenceElementSelectors
    groupedVariableIncidenceElementBlockLength
    groupedVariableIncidenceElementCodeBlock
  apply FiniteBlockIndices.zipWith4_flatMap_broadcastValues
  · exact directSourceFinalGroupedVariableFanSlots_length decider symbols
  · rw [directSourceFinalGroupedVariableFanSlots_length,
      directSourceFinalGroupedNextOccurrenceKeys_length]
  · rw [directSourceFinalGroupedVariableFanSlots_length,
      directSourceFinalGroupedParentIndices_length]

end LeanTrominoes.PeriodicCNFStripReduction

end
