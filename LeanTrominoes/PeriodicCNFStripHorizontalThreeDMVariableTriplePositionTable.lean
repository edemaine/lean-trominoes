/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseAffineVariableTripleScan
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMGlobalTriplePositionTablesComputability

/-! # Finite local tables for horizontal variable triple positions -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalThreeDMTripleVariableDecidableEq

/-- Explicit finite-table position block at one used routed-variable slot. -/
def horizontalThreeDMVariableTriplePositionTableBlockComputed
    (source : PeriodicCNF Nat)
    (entry : RoutedVariable × OccurrenceSlot) : List Cell :=
  let typed := (horizontalNormalizedRoutedFormulaComputed source).erase
  let origin := horizontalThreeDMVariableOriginComputed source entry.1
  let polarity := occurrencePolarity typed entry.1 entry.2
  match occurrenceConnectorKind typed entry.1 entry.2 with
  | .fixedRed =>
      allFixedRedTriples.map fun triple =>
        Cell.add origin
          (fixedRedTripleSitePositionTable
            ((entry.2, polarity), triple))
  | .fixedGreen =>
      allOrdinaryTriples.map fun triple =>
        Cell.add origin
          (ordinaryTripleSitePositionTable
            (((entry.2, .fixedGreen), polarity), triple))
  | .fixedBlue =>
      allOrdinaryTriples.map fun triple =>
        Cell.add origin
          (ordinaryTripleSitePositionTable
            (((entry.2, .fixedBlue), polarity), triple))

theorem horizontalThreeDMVariableTriplePositionBlockComputed_eq_table
    (source : PeriodicCNF Nat)
    (entry : RoutedVariable × OccurrenceSlot) :
    horizontalThreeDMVariableTriplePositionBlockComputed source entry =
      horizontalThreeDMVariableTriplePositionTableBlockComputed
        source entry := by
  rcases entry with ⟨atom, slot⟩
  unfold horizontalThreeDMVariableTriplePositionBlockComputed
    occurrenceTripleBlock
    horizontalThreeDMVariableTriplePositionTableBlockComputed
  cases connectorEq : occurrenceConnectorKind
      (horizontalNormalizedRoutedFormulaComputed source).erase atom slot <;>
    simp [occurrenceTriples, connectorEq,
      horizontalThreeDMTriplePositionComputed,
      assembledTriplePositionData, orientedTripleLocalPosition,
      ordinaryTripleSitePositionTable, fixedRedTripleSitePositionTable]

@[simp] theorem horizontalThreeDMVariableTriplePositionTableBlockComputed_length
    (source : PeriodicCNF Nat)
    (entry : RoutedVariable × OccurrenceSlot) :
    (horizontalThreeDMVariableTriplePositionTableBlockComputed
      source entry).length =
      horizontalThreeDMVariableTripleBlockWidthComputed source entry := by
  rw [← horizontalThreeDMVariableTriplePositionBlockComputed_eq_table]
  exact horizontalThreeDMVariableTriplePositionBlockComputed_length
    source entry

/-- The complete variable-position prefix can now use only variable origins,
occurrence polarity/kind, and finite local tables. -/
theorem horizontalThreeDMVariableTriplePositionsComputed_eq_tableBlocks
    (source : PeriodicCNF Nat) :
    horizontalThreeDMVariableTriplePositionsComputed source =
      (horizontalThreeDMUsedOccurrenceSlotsComputed source).flatMap
        (horizontalThreeDMVariableTriplePositionTableBlockComputed source) := by
  rw [horizontalThreeDMVariableTriplePositionsComputed_eq_occurrenceBlocks]
  apply List.flatMap_congr
  intro entry _
  exact horizontalThreeDMVariableTriplePositionBlockComputed_eq_table
    source entry

end PeriodicCNFStripReduction
end LeanTrominoes
