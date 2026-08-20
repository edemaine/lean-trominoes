/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.IndexedListScan
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMVariableTripleBlocks
import LeanTrominoes.PeriodicCNFStripDirectSparseAffineTripleRequestBlocks

/-! # Explicit variable-width scan for affine triple requests -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalThreeDMTripleVariableDecidableEq

/-- Stable routed-variable/slot order behind the horizontal variable triple
prefix. -/
def horizontalThreeDMUsedOccurrenceSlotsComputed
    (source : PeriodicCNF Nat) : List (RoutedVariable × OccurrenceSlot) :=
  usedOccurrenceSlots
    (horizontalNormalizedRoutedFormulaComputed source).erase

/-- Fixed connector-position block contributed by one used routed-variable
slot. -/
def horizontalThreeDMVariableTriplePositionBlockComputed
    (source : PeriodicCNF Nat)
    (entry : RoutedVariable × OccurrenceSlot) : List Cell :=
  occurrenceTripleBlock
    (horizontalNormalizedRoutedFormulaComputed source).erase
    (horizontalThreeDMTriplePositionComputed source) entry

/-- Width of that connector block: seven for fixed-red, three otherwise. -/
def horizontalThreeDMVariableTripleBlockWidthComputed
    (source : PeriodicCNF Nat)
    (entry : RoutedVariable × OccurrenceSlot) : Nat :=
  occurrenceTripleBlockWidth
    (horizontalNormalizedRoutedFormulaComputed source).erase entry

@[simp] theorem horizontalThreeDMVariableTriplePositionBlockComputed_length
    (source : PeriodicCNF Nat)
    (entry : RoutedVariable × OccurrenceSlot) :
    (horizontalThreeDMVariableTriplePositionBlockComputed
      source entry).length =
      horizontalThreeDMVariableTripleBlockWidthComputed source entry := by
  exact occurrenceTripleBlock_length
    (horizontalNormalizedRoutedFormulaComputed source).erase
    (horizontalThreeDMTriplePositionComputed source) entry

/-- The variable-position prefix is exactly the stable used-slot scan by its
three- or seven-position connector blocks. -/
theorem horizontalThreeDMVariableTriplePositionsComputed_eq_occurrenceBlocks
    (source : PeriodicCNF Nat) :
    horizontalThreeDMVariableTriplePositionsComputed source =
      (horizontalThreeDMUsedOccurrenceSlotsComputed source).flatMap
        (horizontalThreeDMVariableTriplePositionBlockComputed source) := by
  unfold horizontalThreeDMVariableTriplePositionsComputed
    horizontalThreeDMUsedOccurrenceSlotsComputed
    horizontalThreeDMVariableTriplePositionBlockComputed
  exact variableTriples_map_eq_occurrenceBlocks
    (horizontalNormalizedRoutedFormulaComputed source).erase
    (horizontalThreeDMTriplePositionComputed source)

/-- Explicit variable-module requests, carrying the next stable triple index
across the three- and seven-position connector blocks. -/
def directSparseComputedAffineExplicitVariableTripleRequests
    (source : PeriodicCNF Nat)
    (input : PeriodicThreeDM.NormalizationCompiler.Input) :
    List GadgetSparseAffineVertexTokens.Token :=
  (IndexedListScan.zipIdxFlatMapFrom
      (horizontalThreeDMVariableTriplePositionBlockComputed source) 0
      (horizontalThreeDMUsedOccurrenceSlotsComputed source)).flatMap
    fun tagged =>
      directSparseComputedAffinePositionRequestRecord
        input.drawing.gridSize tagged.1
        (PeriodicThreeDM.NormalizationCompiler.finalVertexCellType
          input (.triple tagged.2))

theorem directSparseComputedAffineVariableTripleRequests_eq_explicit
    (source : PeriodicCNF Nat)
    (input : PeriodicThreeDM.NormalizationCompiler.Input) :
    directSparseComputedAffineVariableTripleRequests source input =
      directSparseComputedAffineExplicitVariableTripleRequests
        source input := by
  unfold directSparseComputedAffineVariableTripleRequests
    directSparseComputedAffineExplicitVariableTripleRequests
  rw [horizontalThreeDMVariableTriplePositionsComputed_eq_occurrenceBlocks]
  exact IndexedListScan.flatMap_zipIdx_flatMap_eq_zipIdxFlatMapFrom_flatMap
    (horizontalThreeDMUsedOccurrenceSlotsComputed source)
    (horizontalThreeDMVariableTriplePositionBlockComputed source) 0
    (fun tagged =>
      directSparseComputedAffinePositionRequestRecord
        input.drawing.gridSize tagged.1
        (PeriodicThreeDM.NormalizationCompiler.finalVertexCellType
          input (.triple tagged.2)))

end PeriodicCNFStripReduction
end LeanTrominoes
