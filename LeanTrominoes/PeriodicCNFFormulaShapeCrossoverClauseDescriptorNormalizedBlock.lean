/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeCrossoverClauseDescriptorBlock

/-! # Descriptors of one physical normalized crossover block -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNF

open PeriodicOrthocrossing

namespace FormulaShapeRetainedPlanarMetadataDirection

/-- Mapping the canonical descriptor function over the normalized block at
one physical crossing recovers one fixed Figure 8(b) descriptor block. -/
theorem normalizedCrossoverBlock_map_descriptor
    {Variable : Type} [DecidableEq Variable]
    (graph : PeriodicGraph (CNFVertex Variable))
    (crossing : CrossingRecord) :
    (normalizedCrossoverBlock graph crossing).map
        canonicalCrossoverClauseDescriptor =
      FormulaShapeCrossoverDirection.descriptors := by
  unfold normalizedCrossoverBlock
  exact canonicalNormalizedCrossoverBlock_map_descriptor
    (crossing.periodNormalize graph)

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes

end
