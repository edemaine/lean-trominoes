/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateBlockAppend
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCrossingCarrierKeySlotData

/-! # Shape-pair decomposition of crossing carrier-key slots -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags
open PaddedSupportedCandidateBlocks

/-- The complete fixed crossing slot scan decomposes into aligned route-shape
pair scans. -/
theorem crossingCarrierKeyActiveValues_eq_shapePairs
    (pair : RouteDescriptor × RouteDescriptor) :
    activeValues
        (crossingCarrierKeyActivations (descriptorPairTokens pair))
        (crossingCarrierKeyTemplateBlocks pair) =
      (allRouteShapes ×ˢ allRouteShapes).flatMap fun shapes =>
        activeValues
          ((routeShapePairCrossingPredicates shapes).map fun predicate =>
            predicate.evalTokens (descriptorPairTokens pair))
          (routeShapePairCrossingCarrierKeyTemplateBlocks pair shapes) := by
  unfold crossingCarrierKeyActivations affineCrossingPredicates
    crossingCarrierKeyTemplateBlocks
  rw [List.map_flatMap, activeValues_flatMap]
  intro shapes _shapesMember
  simp [routeShapePairCrossingPredicates,
    routeShapePairCrossingCarrierKeyTemplateBlocks]

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
