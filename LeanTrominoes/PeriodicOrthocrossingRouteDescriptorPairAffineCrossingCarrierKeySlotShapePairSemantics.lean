/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateBlockMappedSelection
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCrossingCarrierKeySlotValueSemantics

/-! # One shape-pair crossing carrier-key slot semantics -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags
open PaddedSupportedCandidateBlocks

/-- Removing inactive slots from one fixed route-shape-pair scan gives one
complete retained key block for every accepted affine occurrence pair, in
the predicate scan's exact order. -/
theorem routeShapePairCrossingCarrierKeyActiveValues_eq
    (shapes : RouteShape × RouteShape)
    (pair : RouteDescriptor × RouteDescriptor) :
    activeValues
        ((routeShapePairCrossingPredicates shapes).map fun predicate =>
          predicate.evalTokens (descriptorPairTokens pair))
        (routeShapePairCrossingCarrierKeyTemplateBlocks pair shapes) =
      ((shapes.1.occurrences .first ×ˢ
          shapes.2.occurrences .second).filter fun occurrences =>
        (guardedCrossingPredicate shapes occurrences).evalTokens
          (descriptorPairTokens pair)).flatMap fun occurrences =>
            occurrencePairCarrierKeyBlock
              (occurrences.1.evalPair .first pair,
                occurrences.2.evalPair .second pair) := by
  unfold routeShapePairCrossingPredicates
    routeShapePairCrossingCarrierKeyTemplateBlocks
  rw [List.map_map]
  change activeValues
      (((shapes.1.occurrences .first ×ˢ
          shapes.2.occurrences .second).map fun occurrences =>
        (guardedCrossingPredicate shapes occurrences).evalTokens
          (descriptorPairTokens pair)))
      ((shapes.1.occurrences .first ×ˢ
          shapes.2.occurrences .second).map fun occurrences =>
        occurrencePairCrossingCarrierKeyTemplateBlock pair occurrences) = _
  rw [activeValues_map_eq_filter_flatMap]
  apply List.flatMap_congr
  intro occurrences _occurrencesMember
  exact occurrencePairCrossingCarrierKeyTemplateBlock_values
    pair occurrences

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
