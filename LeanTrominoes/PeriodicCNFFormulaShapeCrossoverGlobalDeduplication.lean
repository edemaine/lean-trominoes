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

/-- Duplicate-free normalized crossover prefix with its equality
implementation fixed at the metadata boundary. -/
def crossoverMetadataNormalizedClausesDedup
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :=
  (crossoverMetadataNormalizedClauses source).dedup

/-- Duplicate-free normalized non-crossover suffix with its equality
implementation fixed at the metadata boundary. -/
def nonCrossoverMetadataNormalizedClausesDedup
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :=
  (nonCrossoverMetadataNormalizedClauses source).dedup

/-- Named form of the global crossover/non-crossover clause split. -/
theorem deduplicatedClauses_eq_named_crossover_append_nonCrossover
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (isLocal : source.incidenceGraph.IsLocal) :
    deduplicatedClauses source =
      crossoverMetadataNormalizedClausesDedup source ++
        nonCrossoverMetadataNormalizedClausesDedup source := by
  unfold crossoverMetadataNormalizedClausesDedup
    nonCrossoverMetadataNormalizedClausesDedup
  exact deduplicatedClauses_eq_crossover_append_nonCrossover
    source wellFormed degree isLocal

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
