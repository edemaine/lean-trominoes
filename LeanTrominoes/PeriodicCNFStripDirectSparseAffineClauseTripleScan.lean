/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.IndexedListScan
import LeanTrominoes.PeriodicCNFStripDirectSparseAffineTripleRequestBlocks

/-! # Explicit fixed-width clause scan for affine triple requests -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open PlanarThreeDM

/-- The fixed nine-position clause-core block at one translated clause
origin. -/
def horizontalThreeDMClauseTriplePositionBlockComputed
    (source : PeriodicCNF Nat) (clauseIndex : Nat) : List Cell :=
  allClauseSets.map fun set =>
    Cell.add (horizontalThreeDMClauseOriginComputed source clauseIndex)
      (X3CClauseOrthogonal.setPosition set)

@[simp] theorem horizontalThreeDMClauseTriplePositionBlockComputed_length
    (source : PeriodicCNF Nat) (clauseIndex : Nat) :
    (horizontalThreeDMClauseTriplePositionBlockComputed
      source clauseIndex).length = 9 := by
  simp [horizontalThreeDMClauseTriplePositionBlockComputed,
    allClauseSets]

/-- Equivalent range-indexed presentation of all clause-core positions. -/
def horizontalThreeDMClauseTriplePositionsRangeComputed
    (source : PeriodicCNF Nat) : List Cell :=
  (List.range
      (horizontalNormalizedRoutedFormulaComputed source).erase.clauses.length).flatMap
    (horizontalThreeDMClauseTriplePositionBlockComputed source)

theorem horizontalThreeDMClauseTriplePositionsComputed_eq_range
    (source : PeriodicCNF Nat) :
    horizontalThreeDMClauseTriplePositionsComputed source =
      horizontalThreeDMClauseTriplePositionsRangeComputed source := by
  unfold horizontalThreeDMClauseTriplePositionsComputed
    horizontalThreeDMClauseTriplePositionsRangeComputed
    horizontalThreeDMClauseTriplePositionBlockComputed
  exact (range_getD_flatMap_eq_zipIdx
    (horizontalNormalizedRoutedFormulaComputed source).erase.clauses []
    (fun (_clause : PeriodicClause RoutedVariable) clauseIndex =>
      allClauseSets.map fun set =>
        Cell.add (horizontalThreeDMClauseOriginComputed source clauseIndex)
          (X3CClauseOrthogonal.setPosition set))).symm

/-- Explicit nine-request clause blocks.  The stable index of local clause
triple `setIndex` is `variablePrefix.length + 9 * clauseIndex + setIndex`. -/
def directSparseComputedAffineExplicitClauseTripleRequests
    (source : PeriodicCNF Nat)
    (input : PeriodicThreeDM.NormalizationCompiler.Input) :
    List GadgetSparseAffineVertexTokens.Token :=
  (List.range
      (horizontalNormalizedRoutedFormulaComputed source).erase.clauses.length).flatMap
    fun clauseIndex =>
      (horizontalThreeDMClauseTriplePositionBlockComputed
          source clauseIndex).zipIdx
          ((horizontalThreeDMVariableTriplePositionsComputed source).length +
            9 * clauseIndex) |>.flatMap fun tagged =>
        directSparseComputedAffinePositionRequestRecord
          input.drawing.gridSize tagged.1
          (PeriodicThreeDM.NormalizationCompiler.finalVertexCellType
            input (.triple tagged.2))

theorem directSparseComputedAffineClauseTripleRequests_eq_explicit
    (source : PeriodicCNF Nat)
    (input : PeriodicThreeDM.NormalizationCompiler.Input) :
    directSparseComputedAffineClauseTripleRequests source input =
      directSparseComputedAffineExplicitClauseTripleRequests source input := by
  unfold directSparseComputedAffineClauseTripleRequests
    directSparseComputedAffineExplicitClauseTripleRequests
  rw [horizontalThreeDMClauseTriplePositionsComputed_eq_range]
  unfold horizontalThreeDMClauseTriplePositionsRangeComputed
  rw [IndexedListScan.range_flatMap_zipIdx_eq_flatMap_zipIdx_fixed
    (horizontalNormalizedRoutedFormulaComputed source).erase.clauses.length
    (horizontalThreeDMClauseTriplePositionBlockComputed source)
    9
    (horizontalThreeDMVariableTriplePositionsComputed source).length
    (horizontalThreeDMClauseTriplePositionBlockComputed_length source)]
  rw [List.flatMap_assoc]

/-- The original indexed triple scan now consists of its variable-module
prefix followed by explicit fixed nine-request clause blocks. -/
theorem directSparseComputedAffineIndexedTripleRequests_eq_variable_explicitClause
    (source : PeriodicCNF Nat)
    (input : PeriodicThreeDM.NormalizationCompiler.Input) :
    directSparseComputedAffineIndexedTripleRequests source input =
      directSparseComputedAffineVariableTripleRequests source input ++
        directSparseComputedAffineExplicitClauseTripleRequests source input := by
  rw [directSparseComputedAffineIndexedTripleRequests_eq_blocks,
    directSparseComputedAffineClauseTripleRequests_eq_explicit]

end PeriodicCNFStripReduction
end LeanTrominoes
