/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverClauseDescriptorBlock
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCrossoverDeduplication

/-! # Semantic descriptors of deduplicated normalized crossover clauses -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNF

open PeriodicOrthocrossing

namespace FormulaShapeRetainedPlanarMetadataDirection

/-- Mapping canonical descriptors over the deduplicated normalized crossover
clauses gives one fixed Figure 8(b) block per canonical crossing. -/
theorem crossoverMetadataNormalizedClauses_dedup_map_descriptor_eq
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (isLocal : source.incidenceGraph.IsLocal) :
    ((crossoverMetadataNormalizedClauses source).dedup).map
        canonicalCrossoverClauseDescriptor =
      (canonicalizedCrossingHalo source.incidenceGraph).flatMap fun _ =>
        FormulaShapeCrossoverDirection.descriptors := by
  rw [crossoverMetadataNormalizedClauses_dedup_eq
    source wellFormed degree isLocal]
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro crossing _crossingMember
  exact canonicalNormalizedCrossoverBlock_map_descriptor crossing

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes

end
