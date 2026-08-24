/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListFlatMapUnique
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCrossingCarrierKeySlotShapePairRejectionSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCrossingCarrierKeySlotShapePairSelectedSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCrossingCarrierKeySlotShapeStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairRouteShapeSelectionSemantics

/-! # Descriptor-pair crossing carrier-key slot semantics -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags
open PaddedSupportedCandidateBlocks

/-- On two locally selected descriptors, the complete fixed shape-pair scan
emits the exact retained key expansion of their pair-local crossings. -/
theorem crossingCarrierKeyActiveValues_eq_of_matches
    (firstShape secondShape : RouteShape)
    (pair : RouteDescriptor × RouteDescriptor)
    (firstMatches : firstShape.Matches pair.1)
    (secondMatches : secondShape.Matches pair.2) :
    activeValues
        (crossingCarrierKeyActivations (descriptorPairTokens pair))
        (crossingCarrierKeyTemplateBlocks pair) =
      occurrencePairCarrierKeyScan
        (routeDescriptorPairLinearCrossingOccurrencePairsAtPeriod
          pair.1.gridSize pair) := by
  rw [crossingCarrierKeyActiveValues_eq_shapePairs]
  rw [List.flatMap_eq_selected_of_unique
    (allRouteShapes ×ˢ allRouteShapes)
    (fun shapes =>
      activeValues
        ((routeShapePairCrossingPredicates shapes).map fun predicate =>
          predicate.evalTokens (descriptorPairTokens pair))
        (routeShapePairCrossingCarrierKeyTemplateBlocks pair shapes))
    (firstShape, secondShape)
    (allRouteShapes_nodup.product allRouteShapes_nodup)
    (List.mem_product.mpr
      ⟨mem_allRouteShapes firstShape, mem_allRouteShapes secondShape⟩)]
  · exact routeShapePairCrossingCarrierKeyActiveValues_selected_eq
      (firstShape, secondShape) pair firstMatches secondMatches
  · intro shapes _shapesMember shapesNe
    apply
      routeShapePairCrossingCarrierKeyActiveValues_eq_nil_of_not_matches
    intro shapeMatches
    apply shapesNe
    apply Prod.ext
    · exact RouteShape.eq_of_matches shapeMatches.1 firstMatches
    · exact RouteShape.eq_of_matches shapeMatches.2 secondMatches

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
