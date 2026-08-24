/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierDescriptorTemplateData

/-! # Finite descriptor scan for retained carrier-link bits -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

/-- Expand an ordered stream of carrier-link bits into the corresponding
two-token implication blocks. -/
def carrierLinkDescriptorScan (linkBits : List (Bool × Bool)) :
    List FormulaShapeDirectionOrdering.Token :=
  linkBits.flatMap fun bits =>
    compiledCarrierLinkDescriptorBlock bits.1 bits.2

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
