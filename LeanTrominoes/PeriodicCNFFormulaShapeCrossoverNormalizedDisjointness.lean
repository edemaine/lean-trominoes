/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverInternalClassifierFamily
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverInternalNonCrossoverFamily

/-! # Disjointness of normalized crossover and non-crossover clauses -/

namespace LeanTrominoes
namespace PeriodicCNF

namespace FormulaShapeRetainedPlanarMetadataDirection

/-- No normalized crossover clause is equal to a normalized clause from any
of the other four retained metadata families. -/
theorem crossoverMetadataNormalizedClauses_disjoint_nonCrossover
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (isLocal : source.incidenceGraph.IsLocal) :
    List.Disjoint
      (crossoverMetadataNormalizedClauses source)
      (nonCrossoverMetadataNormalizedClauses source) := by
  rw [List.disjoint_left]
  intro clause crossoverMember nonCrossoverMember
  have hasInternal :=
    crossoverMetadataNormalizedClause_hasCrossoverInternal
      source wellFormed degree isLocal clause crossoverMember
  have hasNoInternal :=
    nonCrossoverMetadataNormalizedClause_hasCrossoverInternal_eq_false
      source clause nonCrossoverMember
  rw [hasNoInternal] at hasInternal
  exact Bool.false_ne_true hasInternal

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
