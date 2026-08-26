/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierLinkScanData
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderedRetainedPairData

/-! # Rank-ordered retained carrier-link descriptor scan -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

/-- Decode the sparse rank-ordered carrier-pair stream and expand every
surviving axis/next-slice pair to its fixed two-token descriptor block. -/
def rankOrderedCarrierLinkDescriptorScan
    (descriptors : List PeriodicOrthocrossing.RouteDescriptor) :
    List FormulaShapeDirectionOrdering.Token :=
  carrierLinkDescriptorScan
    (PeriodicOrthocrossing.CarrierRankOrderedPairs.retainedPairBits
      descriptors)

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
