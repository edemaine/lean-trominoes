/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeDirectionOrderingTokenData
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierRouteDirectionData

/-! # Static retained carrier implication descriptors -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open UnaryProgramClauseProfile

/-- The finite direction-aware descriptor of one compiled carrier
implication. -/
def compiledCarrierClauseDescriptor
    (horizontal nextSlice forward : Bool) :
    FormulaShapeDirectionOrdering.Token :=
  match forward with
  | true =>
      .clause (.binary
        ⟨false, true⟩ (compiledCarrierLensRouteFirstDirection horizontal 0 0)
        ⟨nextSlice, false⟩ (compiledCarrierLensRouteFirstDirection horizontal 0 1))
  | false =>
      .clause (.binary
        ⟨false, false⟩ (compiledCarrierLensRouteFirstDirection horizontal 1 0)
        ⟨nextSlice, true⟩ (compiledCarrierLensRouteFirstDirection horizontal 1 1))

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
