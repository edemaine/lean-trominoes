/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverInternalClassifierFixed
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCrossoverNormalizedFamily

/-! # Internal atoms in a canonical normalized crossover block -/

namespace LeanTrominoes
namespace PeriodicCNF

open PeriodicOrthocrossing

namespace FormulaShapeRetainedPlanarMetadataDirection

/-- Every clause in a canonical normalized crossover block contains a
crossover-internal atom. -/
theorem canonicalNormalizedCrossoverBlock_hasCrossoverInternal_of_mem
    {Variable : Type}
    (crossing : CrossingRecord)
    (clause :
      PeriodicClause (WrappedPeriodicPlanarSATVariable Variable))
    (clauseMember :
      clause ∈ canonicalNormalizedCrossoverBlock crossing) :
    normalizedClauseHasCrossoverInternal clause = true := by
  unfold canonicalNormalizedCrossoverBlock at clauseMember
  rcases List.mem_map.mp clauseMember with
    ⟨taggedClause, taggedClauseMember, rfl⟩
  exact wrappedNormalizedClause_hasCrossoverInternal
    crossing taggedClause.1
      (List.fst_mem_of_mem_zipIdx taggedClauseMember)

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
