/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseAffineClauseTripleScan
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMClauseCellTypeAt

/-! # Finite-table clause scan for affine triple requests -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open PlanarThreeDM

/-- Clause-triple requests expressed solely through translated positions and
the fixed finite clause cell-type table. -/
def directSparseComputedAffineTableClauseTripleRequests
    (source : PeriodicCNF Nat) :
    List GadgetSparseAffineVertexTokens.Token :=
  (List.range
      (horizontalNormalizedRoutedFormulaComputed source).erase.clauses.length).flatMap
    fun clauseIndex =>
      allClauseSets.zipIdx.flatMap fun taggedSet =>
        directSparseComputedAffinePositionRequestRecord
          (horizontalNormalizationInputComputed source).drawing.gridSize
          (Cell.add (horizontalThreeDMClauseOriginComputed source clauseIndex)
            (X3CClauseOrthogonal.setPosition taggedSet.1))
          (horizontalClauseTripleCellTypeComputed taggedSet.1)

/-- The canonical explicit clause scan at the horizontal normalization input
is exactly the fixed finite-table scan. -/
theorem directSparseComputedAffineExplicitClauseTripleRequests_eq_table
    (source : PeriodicCNF Nat) :
    directSparseComputedAffineExplicitClauseTripleRequests
        source (horizontalNormalizationInputComputed source) =
      directSparseComputedAffineTableClauseTripleRequests source := by
  unfold directSparseComputedAffineExplicitClauseTripleRequests
    directSparseComputedAffineTableClauseTripleRequests
  apply List.flatMap_congr
  intro clauseIndex clauseIndexMember
  apply List.flatMap_congr
  intro taggedSet setMember
  rw [horizontalFinalClauseTripleCellTypeAtComputed_eq_table
    source clauseIndex (List.mem_range.mp clauseIndexMember)
    taggedSet.1 taggedSet.2 setMember]

end PeriodicCNFStripReduction
end LeanTrominoes
