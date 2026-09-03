/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableIncidenceBodyPointwiseSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableIncidenceOccurrenceBlockIndexSemantics

/-! # Occurrence blocks of complete grouped variable-incidence bodies -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- The complete direct variable-body presentation is a flattening of the
same occurrence blocks as its finite prefixes.  Stable global indices are
retained inside each block, so routed suffix selection is unchanged. -/
theorem directSourceFinalGroupedVariableIncidenceBodies_eq_occurrenceBlocks
    (symbols : List encoding.Γ) :
    directSourceFinalGroupedVariableIncidenceBodies decider symbols =
      (List.zipWith
        (fun blockStart pair =>
          (groupedVariableIncidencePrefixQueryBlock pair).zipIdx
              (3 * blockStart) |>.map fun tagged =>
            HorizontalFiniteIncidenceDirectionQuery.directions tagged.1 ++
              if tagged.2 ∈
                  directSourceFinalGroupedRoutedIncidenceKeys
                    decider symbols then
                FiniteAlphabetKeyedDelimitedBlockLookup.alignedBody
                  (directSourceFinalGroupedRoutedIncidenceKeys
                    decider symbols)
                  (directSourceFinalGroupedColoredOccurrenceDirectionBodies
                    decider symbols)
                  tagged.2
              else [])
        (directSourceFinalGroupedOccurrenceTripleBlockStarts
          decider symbols)
        (directSourceFinalGroupedVariableFanSlots decider symbols)).flatten := by
  rw [directSourceFinalGroupedVariableIncidenceBodies_eq_pointwise,
    directSourceFinalGroupedVariableIncidencePrefixQueries_zipIdx_eq_occurrenceBlocks,
    List.map_flatten, List.map_zipWith]

end LeanTrominoes.PeriodicCNFStripReduction

end
