/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverGlobalDeduplication
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverRepresentativeDescriptorMap

/-! # Crossover prefix of representative clause descriptors -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNF

namespace FormulaShapeRetainedPlanarMetadataDirection

/-- Representative clause descriptors begin with canonical descriptors of
the globally retained crossover clauses. -/
theorem representativeClauseDescriptors_eq_crossover_append_nonCrossover
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (isLocal : source.incidenceGraph.IsLocal) :
    representativeClauseDescriptors source =
      ((crossoverMetadataNormalizedClauses source).dedup).map
          canonicalCrossoverClauseDescriptor ++
        ((nonCrossoverMetadataNormalizedClauses source).dedup).map
          (representativeClauseDescriptor source) := by
  unfold representativeClauseDescriptors
  rw [deduplicatedClauses_eq_crossover_append_nonCrossover
    source wellFormed degree isLocal]
  rw [List.map_append]
  rw [crossoverMetadataNormalizedClauses_dedup_map_representative_eq
    source wellFormed degree isLocal]

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes

end
