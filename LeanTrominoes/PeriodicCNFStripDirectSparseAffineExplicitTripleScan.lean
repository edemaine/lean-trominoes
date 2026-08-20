/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripDirectSparseAffineClauseTripleScan
import LeanTrominoes.PeriodicCNFStripDirectSparseAffineVariableTripleScan

/-! # Complete explicit affine triple-request scan -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

/-- The original indexed triple request stream is exactly the variable-width
used-slot scan followed by the fixed nine-request block of every clause. -/
theorem directSparseComputedAffineIndexedTripleRequests_eq_explicitBlocks
    (source : PeriodicCNF Nat)
    (input : PeriodicThreeDM.NormalizationCompiler.Input) :
    directSparseComputedAffineIndexedTripleRequests source input =
      directSparseComputedAffineExplicitVariableTripleRequests source input ++
        directSparseComputedAffineExplicitClauseTripleRequests source input := by
  rw [directSparseComputedAffineIndexedTripleRequests_eq_variable_explicitClause,
    directSparseComputedAffineVariableTripleRequests_eq_explicit]

end PeriodicCNFStripReduction
end LeanTrominoes
