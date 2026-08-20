/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseAffineClauseTripleTableScan
import LeanTrominoes.PeriodicCNFStripDirectSparseAffineVariableTripleCellTableScan

/-! # Complete finite-table affine triple request scan -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

/-- At the horizontal normalization input, the complete indexed triple scan
is the typed variable-table prefix followed by the fixed clause-table suffix. -/
theorem directSparseComputedAffineIndexedTripleRequests_eq_cellTables
    (source : PeriodicCNF Nat) :
    directSparseComputedAffineIndexedTripleRequests
        source (horizontalNormalizationInputComputed source) =
      directSparseComputedAffineTypedTableVariableTripleRequests source ++
        directSparseComputedAffineTableClauseTripleRequests source := by
  rw [directSparseComputedAffineIndexedTripleRequests_eq_variable_explicitClause,
    directSparseComputedAffineVariableTripleRequests_eq_cellTable,
    directSparseComputedAffineExplicitClauseTripleRequests_eq_table]

end PeriodicCNFStripReduction
end LeanTrominoes
