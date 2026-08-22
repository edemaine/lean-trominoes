/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverNormalizedDisjointness
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverNormalizedPrefix

/-! # Crossover prefix of globally deduplicated retained clauses -/

namespace LeanTrominoes
namespace PeriodicCNF

namespace FormulaShapeRetainedPlanarMetadataDirection

/-- Global last-occurrence-preserving deduplication splits across the disjoint
crossover prefix and four-family suffix. -/
theorem deduplicatedClauses_eq_crossover_append_nonCrossover
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (isLocal : source.incidenceGraph.IsLocal) :
    deduplicatedClauses source =
      (crossoverMetadataNormalizedClauses source).dedup ++
        (nonCrossoverMetadataNormalizedClauses source).dedup := by
  unfold deduplicatedClauses
  rw [normalizedClauses_eq_crossover_append_nonCrossover source]
  exact
    (crossoverMetadataNormalizedClauses_disjoint_nonCrossover
      source wellFormed degree isLocal).dedup_append

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
