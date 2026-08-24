/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierClauseDescriptorTemplateData

/-! # Static retained carrier descriptor templates -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

/-- Fixed two-token block determined by one retained carrier link's two
finite bits. -/
def compiledCarrierLinkDescriptorBlock
    (horizontal nextSlice : Bool) :
    List FormulaShapeDirectionOrdering.Token :=
  [compiledCarrierClauseDescriptor horizontal nextSlice true,
    compiledCarrierClauseDescriptor horizontal nextSlice false]

@[simp] theorem compiledCarrierLinkDescriptorBlock_length
    (horizontal nextSlice : Bool) :
    (compiledCarrierLinkDescriptorBlock horizontal nextSlice).length = 2 :=
  rfl

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
