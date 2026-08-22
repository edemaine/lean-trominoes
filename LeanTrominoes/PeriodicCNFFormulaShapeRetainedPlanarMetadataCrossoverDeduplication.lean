/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverCanonicalBlockDeduplication
import LeanTrominoes.PeriodicOrthocrossingCanonicalizedCrossingHalo

/-! # Exact deduplication of retained crossover clauses -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing

/-- Last-occurrence-preserving clause deduplication removes exactly the
repeated physical copies of canonical crossover blocks. -/
theorem crossoverMetadataNormalizedClauses_dedup_eq
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (isLocal : source.incidenceGraph.IsLocal) :
    (crossoverMetadataNormalizedClauses source).dedup =
      (canonicalizedCrossingHalo source.incidenceGraph).flatMap
        (@canonicalNormalizedCrossoverBlock Variable) := by
  rw [crossoverMetadataNormalizedClauses_eq_blocks
    source wellFormed degree isLocal]
  unfold normalizedCrossoverBlock
  rw [← List.flatMap_map,
    dedup_flatMap_canonicalNormalizedCrossoverBlock]
  rfl

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
