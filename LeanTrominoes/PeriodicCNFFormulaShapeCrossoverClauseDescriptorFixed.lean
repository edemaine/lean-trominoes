/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverClauseDescriptorDedup

/-! # Fixed stream of deduplicated crossover descriptors -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNF

open PeriodicOrthocrossing

namespace FormulaShapeRetainedPlanarMetadataDirection

/-- The descriptors of the deduplicated normalized crossover clauses are
the fixed Figure 8(b) block repeated once per canonical oriented crossing. -/
theorem crossoverMetadataNormalizedClauses_dedup_map_descriptor_eq_fixed
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (isLocal : source.incidenceGraph.IsLocal) :
    ((crossoverMetadataNormalizedClauses source).dedup).map
        canonicalCrossoverClauseDescriptor =
      (List.replicate
        (orientedCrossings source.incidenceGraph).length
        FormulaShapeCrossoverDirection.descriptors).flatten := by
  rw [crossoverMetadataNormalizedClauses_dedup_map_descriptor_eq
    source wellFormed degree isLocal]
  have constantBlocks (crossings : List CrossingRecord) :
      crossings.flatMap (fun _ =>
          FormulaShapeCrossoverDirection.descriptors) =
        (List.replicate crossings.length
          FormulaShapeCrossoverDirection.descriptors).flatten := by
    induction crossings with
    | nil => rfl
    | cons crossing crossings induction =>
      simp only [List.flatMap_cons, List.length_cons,
        List.replicate_succ, List.flatten_cons, induction]
  rw [constantBlocks, canonicalizedCrossingHalo_length
    wellFormed degree isLocal]

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes

end
