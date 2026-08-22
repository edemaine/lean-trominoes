/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverInternalCarrierBend
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverInternalNormalization
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverInternalRouted
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverNormalizedPrefixData

/-! # Normalized non-crossover clauses contain no crossover internals -/

namespace LeanTrominoes
namespace PeriodicCNF

open PeriodicOrthocrossing

namespace FormulaShapeRetainedPlanarMetadataDirection

/-- Every normalized clause in the four-family non-crossover suffix contains
no crossover-internal atom. -/
theorem nonCrossoverMetadataNormalizedClause_hasCrossoverInternal_eq_false
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (clause :
      PeriodicClause (WrappedPeriodicPlanarSATVariable Variable))
    (clauseMember :
      clause ∈ nonCrossoverMetadataNormalizedClauses source) :
    normalizedClauseHasCrossoverInternal clause = false := by
  unfold nonCrossoverMetadataNormalizedClauses at clauseMember
  rcases List.mem_map.mp clauseMember with
    ⟨metadata, metadataMember, rfl⟩
  rw [normalizedClause_hasCrossoverInternal_eq_embeddedClause]
  simp only [List.mem_append] at metadataMember
  rcases metadataMember with
      ((carrierMember | bendMember) | routedClauseMember) |
        routedVariableMember
  · exact retainedCarrierMetadataClause_hasCrossoverInternal_eq_false
      source metadata carrierMember
  · exact bendMetadataClause_hasCrossoverInternal_eq_false
      source metadata bendMember
  · exact routedClauseMetadataClause_hasCrossoverInternal_eq_false
      source metadata routedClauseMember
  · exact routedVariableMetadataClause_hasCrossoverInternal_eq_false
      source metadata routedVariableMember

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
