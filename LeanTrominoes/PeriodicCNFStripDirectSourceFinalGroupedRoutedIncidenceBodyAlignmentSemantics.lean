/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedRoutedIncidenceKeyNodup
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedColoredOccurrenceDirectionBlockListSemantics

/-! # Alignment of grouped routed-incidence keys and bodies -/

noncomputable section

namespace LeanTrominoes.PeriodicCNFStripReduction

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- Mapping every grouped routed-incidence key to its uniquely aligned body
recovers the RGB occurrence-body stream in its original order. -/
theorem
    directSourceFinalGroupedColoredOccurrenceDirectionBodies_eq_map_alignedBody
    (symbols : List encoding.Γ) :
    directSourceFinalGroupedColoredOccurrenceDirectionBodies
        decider symbols =
      (directSourceFinalGroupedRoutedIncidenceKeys
        decider symbols).map
        (FiniteAlphabetKeyedDelimitedBlockLookup.alignedBody
          (directSourceFinalGroupedRoutedIncidenceKeys decider symbols)
          (directSourceFinalGroupedColoredOccurrenceDirectionBodies
            decider symbols)) := by
  exact FiniteAlphabetKeyedDelimitedBlockLookup.bodies_eq_map_alignedBody
    (directSourceFinalGroupedRoutedIncidenceKeys decider symbols)
    (directSourceFinalGroupedColoredOccurrenceDirectionBodies decider symbols)
    (directSourceFinalGroupedColoredOccurrenceDirectionBodies_length_eq_keys
      decider symbols).symm
    (directSourceFinalGroupedRoutedIncidenceKeys_nodup decider symbols)

end LeanTrominoes.PeriodicCNFStripReduction

end
