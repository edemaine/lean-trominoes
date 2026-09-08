/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman
-/
import LeanTrominoes.PeriodicCNFStripGroupedVariableIncidenceLocalColumnTypedShape
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableIncidenceLocalColumnValiditySemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableIncidenceOccurrenceBlockBodySemantics

/-! # Complete variable-incidence bodies are flattened local columns -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- The existing global body stream is exactly the concatenation of its
valid occurrence-local columns. -/
theorem directSourceFinalGroupedVariableIncidenceBodies_eq_localColumns
    (symbols : List encoding.Γ) :
    directSourceFinalGroupedVariableIncidenceBodies decider symbols =
      ((directSourceFinalGroupedVariableIncidenceLocalColumns decider symbols).map
        GroupedVariableIncidenceLocalColumn.localBodyBlock).flatten := by
  rw [directSourceFinalGroupedVariableIncidenceBodies_eq_occurrenceBlocks,
    ← directSourceFinalGroupedVariableIncidenceGlobalBodyBlocks_eq_localBodyBlocks]
  have projected := GroupedVariableIncidenceLocalColumn.map_globalBodyBlock_zipWith4
    (directSourceFinalGroupedRoutedIncidenceKeys decider symbols)
    (directSourceFinalGroupedColoredOccurrenceDirectionBodies decider symbols)
    (directSourceFinalGroupedOccurrenceTripleBlockStarts decider symbols)
    (directSourceFinalGroupedVariableFanSlots decider symbols)
    (directSourceFinalGroupedOccurrenceData decider symbols)
    (directSourceFinalGroupedOccurrenceDirectionBodyBlocks decider symbols)
    (directSourceFinalGroupedOccurrenceTripleBlockStarts_length decider symbols)
    ((directSourceFinalGroupedOccurrenceTripleBlockStarts_length decider symbols).trans
      (directSourceFinalGroupedOccurrenceDirectionBodyBlocks_length decider symbols).symm)
  simpa only [directSourceFinalGroupedVariableIncidenceLocalColumns] using
    (congrArg List.flatten projected).symm

end LeanTrominoes.PeriodicCNFStripReduction

end
