/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataDescriptorBlockData

/-! # Clause and variable blocks of retained metadata descriptors -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

/-- The exact metadata descriptor stream is its clause block followed by its
distinct-variable marker block. -/
theorem descriptors_eq_blocks
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    descriptors source =
      clauseDescriptors source ++ variableMarkers source := by
  unfold descriptors FormulaShapeDirectionOrdering.ofFormula
    clauseDescriptors variableMarkers
  rfl

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
