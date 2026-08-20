/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseAffineClauseTripleScan
import LeanTrominoes.PeriodicCNFStripHorizontalThreeDMVariableTriplePositionTable

/-! # Finite-table variable scan for affine triple requests -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

/-- Variable-module requests expressed solely through the stable used-slot
list, carried stable index, variable origin, occurrence polarity/kind, and
finite local position tables. -/
def directSparseComputedAffineTableVariableTripleRequests
    (source : PeriodicCNF Nat)
    (input : PeriodicThreeDM.NormalizationCompiler.Input) :
    List GadgetSparseAffineVertexTokens.Token :=
  (IndexedListScan.zipIdxFlatMapFrom
      (horizontalThreeDMVariableTriplePositionTableBlockComputed source) 0
      (horizontalThreeDMUsedOccurrenceSlotsComputed source)).flatMap
    fun tagged =>
      directSparseComputedAffinePositionRequestRecord
        input.drawing.gridSize tagged.1
        (PeriodicThreeDM.NormalizationCompiler.finalVertexCellType
          input (.triple tagged.2))

theorem directSparseComputedAffineVariableTripleRequests_eq_table
    (source : PeriodicCNF Nat)
    (input : PeriodicThreeDM.NormalizationCompiler.Input) :
    directSparseComputedAffineVariableTripleRequests source input =
      directSparseComputedAffineTableVariableTripleRequests
        source input := by
  unfold directSparseComputedAffineVariableTripleRequests
    directSparseComputedAffineTableVariableTripleRequests
  rw [horizontalThreeDMVariableTriplePositionsComputed_eq_tableBlocks]
  exact IndexedListScan.flatMap_zipIdx_flatMap_eq_zipIdxFlatMapFrom_flatMap
    (horizontalThreeDMUsedOccurrenceSlotsComputed source)
    (horizontalThreeDMVariableTriplePositionTableBlockComputed source) 0
    (fun tagged =>
      directSparseComputedAffinePositionRequestRecord
        input.drawing.gridSize tagged.1
        (PeriodicThreeDM.NormalizationCompiler.finalVertexCellType
          input (.triple tagged.2)))

/-- Complete explicit triple scan using finite-table variable blocks and fixed
nine-position clause blocks. -/
theorem directSparseComputedAffineIndexedTripleRequests_eq_tableBlocks
    (source : PeriodicCNF Nat)
    (input : PeriodicThreeDM.NormalizationCompiler.Input) :
    directSparseComputedAffineIndexedTripleRequests source input =
      directSparseComputedAffineTableVariableTripleRequests source input ++
        directSparseComputedAffineExplicitClauseTripleRequests source input := by
  rw [directSparseComputedAffineIndexedTripleRequests_eq_variable_explicitClause,
    directSparseComputedAffineVariableTripleRequests_eq_table]

end PeriodicCNFStripReduction
end LeanTrominoes
