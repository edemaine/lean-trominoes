/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListDedupDisjointBlocks
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverNormalizedBlockDistinctness

/-! # Deduplication of canonical crossover blocks -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

/-- The generic disjoint-block lemma specialized to canonical wrapped
crossover clause blocks. -/
theorem dedup_flatMap_canonicalNormalizedCrossoverBlock
    {Variable : Type}
    [DecidableEq Variable]
    (crossings : List PeriodicOrthocrossing.CrossingRecord) :
    (crossings.flatMap
      (@canonicalNormalizedCrossoverBlock Variable)).dedup =
      crossings.dedup.flatMap
        (@canonicalNormalizedCrossoverBlock Variable) := by
  exact List.dedup_flatMap_blocks
    crossings
    (@canonicalNormalizedCrossoverBlock Variable)
    canonicalNormalizedCrossoverBlock_nodup
    canonicalNormalizedCrossoverBlock_disjoint

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
