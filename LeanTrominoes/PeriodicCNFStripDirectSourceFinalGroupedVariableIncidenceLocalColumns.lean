/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListZipWithFourSemantics
import LeanTrominoes.PeriodicCNFStripDirectSourceFinalGroupedVariableIncidenceLocalBodyBlockSourceSemantics
import LeanTrominoes.PeriodicCNFStripGroupedVariableIncidenceLocalColumnSemantics

/-! # Aligned source columns for grouped variable-incidence bodies -/

noncomputable section

set_option maxHeartbeats 800000

namespace LeanTrominoes.PeriodicCNFStripReduction

open GroupedRoutedIncidenceKeyLocality

variable {Input : Type}
variable {encoding : _root_.Computability.FinEncoding Input}
variable {language : Input → Prop}
variable (decider : Complexity.DeciderInPolySpace encoding language)

/-- The coherent RGB body block selected at each grouped occurrence. -/
def directSourceFinalGroupedOccurrenceDirectionBodyBlocks
    (symbols : List encoding.Γ) : List (List (List AxisDirection)) :=
  (directSourceFinalGroupedOccurrenceIndices decider symbols).map fun index =>
    (List.zipWith directFinalOccurrenceDirectionBodyBlock
      (directSourceFinalOccurrenceFramesExpected decider symbols)
      (directFigureNinePolarityRoutePairs decider symbols)).getD index []

/-- The starts, grouped fan slots, occurrence data, and RGB body blocks used
by the local variable-incidence comparison, zipped into opaque columns. -/
def directSourceFinalGroupedVariableIncidenceLocalColumns
    (symbols : List encoding.Γ) :
    List GroupedVariableIncidenceLocalColumn :=
  List.zipWith4 GroupedVariableIncidenceLocalColumn.mk
    (directSourceFinalGroupedOccurrenceTripleBlockStarts decider symbols)
    (directSourceFinalGroupedVariableFanSlots decider symbols)
    (directSourceFinalGroupedOccurrenceData decider symbols)
    (directSourceFinalGroupedOccurrenceDirectionBodyBlocks decider symbols)

theorem directSourceFinalGroupedOccurrenceDirectionBodyBlocks_length
    (symbols : List encoding.Γ) :
    (directSourceFinalGroupedOccurrenceDirectionBodyBlocks
      decider symbols).length =
      (directSourceFinalGroupedOccurrenceData decider symbols).length := by
  have aligned :=
    directSourceFinalGroupedRoutedIncidenceBodyBlocks_aligned decider symbols
  unfold directSourceFinalGroupedOccurrenceDirectionBodyBlocks
  rw [← aligned.length_eq]
  simp

/-- The source's routed key/body alignment in terms of the named occurrence
body-block column. -/
theorem directSourceFinalGroupedRoutedIncidenceBodyBlocks_aligned_localColumns
    (symbols : List encoding.Γ) :
    List.Forall₂
      (fun keyBlock bodyBlock =>
        keyBlock.map
          (FiniteAlphabetKeyedDelimitedBlockLookup.alignedBody
            (directSourceFinalGroupedRoutedIncidenceKeys decider symbols)
            (directSourceFinalGroupedColoredOccurrenceDirectionBodies
              decider symbols)) = bodyBlock)
      (List.zipWith keyBlock
        (directSourceFinalGroupedOccurrenceTripleBlockStarts decider symbols)
        (directSourceFinalGroupedOccurrenceData decider symbols))
      (directSourceFinalGroupedOccurrenceDirectionBodyBlocks
        decider symbols) := by
  unfold directSourceFinalGroupedOccurrenceDirectionBodyBlocks
  change List.Forall₂ _
    (List.zipWith
      (fun start data =>
        (directFinalOccurrenceRoutedIncidenceKeyOffsets data).map
          fun offset => start * 3 + offset)
      (directSourceFinalGroupedOccurrenceTripleBlockStarts decider symbols)
      (directSourceFinalGroupedOccurrenceData decider symbols)) _
  exact directSourceFinalGroupedRoutedIncidenceBodyBlocks_aligned
    decider symbols

end LeanTrominoes.PeriodicCNFStripReduction

end
