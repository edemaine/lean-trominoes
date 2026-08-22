/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverNormalizedPrefixData

/-! # Crossover prefix of normalized retained clauses -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing

/-- The normalized crossover family is the exact prefix of all normalized
retained metadata clauses. -/
theorem normalizedClauses_eq_crossover_append_nonCrossover
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    normalizedClauses source =
      crossoverMetadataNormalizedClauses source ++
        nonCrossoverMetadataNormalizedClauses source := by
  unfold normalizedClauses retainedDrawingPlanarSATClauseMetadata
    crossoverMetadataNormalizedClauses
    nonCrossoverMetadataNormalizedClauses
  simp only [List.map_append, List.append_assoc]

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
