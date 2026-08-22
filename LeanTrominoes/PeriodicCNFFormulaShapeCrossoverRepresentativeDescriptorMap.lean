/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverRepresentativeDescriptor

/-! # Representative descriptor map on deduplicated crossover clauses -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNF

namespace FormulaShapeRetainedPlanarMetadataDirection

/-- Mapping the public representative selector over the retained crossover
clauses agrees pointwise with the canonical crossover descriptor function. -/
theorem crossoverMetadataNormalizedClauses_dedup_map_representative_eq
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (isLocal : source.incidenceGraph.IsLocal) :
    ((crossoverMetadataNormalizedClauses source).dedup).map
        (representativeClauseDescriptor source) =
      ((crossoverMetadataNormalizedClauses source).dedup).map
        canonicalCrossoverClauseDescriptor := by
  apply List.map_congr_left
  intro clause clauseMember
  apply representativeClauseDescriptor_eq_canonical_of_crossover_mem
    source wellFormed degree isLocal clause
  simpa only [List.mem_dedup] using clauseMember

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes

end
