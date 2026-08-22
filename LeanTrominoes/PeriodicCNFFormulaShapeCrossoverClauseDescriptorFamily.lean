/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverClauseDescriptorNormalizedBlock

/-! # Semantic descriptors of the raw normalized crossover family -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNF

open PeriodicOrthocrossing

namespace FormulaShapeRetainedPlanarMetadataDirection

/-- The raw crossover metadata descriptor stream is obtained by mapping the
canonical descriptor function over the raw normalized crossover clauses. -/
theorem crossoverMetadataClauseDescriptors_eq_map_canonicalDescriptor
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (isLocal : source.incidenceGraph.IsLocal) :
    crossoverMetadataClauseDescriptors source =
      (crossoverMetadataNormalizedClauses source).map
        canonicalCrossoverClauseDescriptor := by
  rw [crossoverMetadataClauseDescriptors_eq_fixedHalo
    source wellFormed degree isLocal]
  rw [crossoverMetadataNormalizedClauses_eq_blocks
    source wellFormed degree isLocal]
  rw [List.map_flatMap]
  unfold fixedHaloCrossoverClauseDescriptors
  apply List.flatMap_congr
  intro crossing _crossingMember
  exact (normalizedCrossoverBlock_map_descriptor
    source.incidenceGraph crossing).symm

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes

end
