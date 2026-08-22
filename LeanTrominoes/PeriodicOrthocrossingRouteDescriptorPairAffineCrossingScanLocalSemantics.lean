/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListFilteredProductMapCount
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCrossingScan
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCrossingSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairLinearCrossing
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairRouteShapeSelectionSemantics

/-! # Exact local semantics of the finite affine crossing scan -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags

/-- A shape pair is enabled on canonical tagged tokens exactly when both
shapes match their respective semantic descriptors. -/
theorem routeShapePairEnabled_descriptorPairTokens
    (shapes : RouteShape × RouteShape)
    (pair : RouteDescriptor × RouteDescriptor) :
    routeShapePairEnabled (descriptorPairTokens pair) shapes = true ↔
      shapes.1.Matches pair.1 ∧ shapes.2.Matches pair.2 := by
  unfold routeShapePairEnabled
  rw [shapes.1.evalTokens_guard, shapes.2.evalTokens_guard]
  simp [descriptorAt]

/-- Once its two route guards hold, one fixed shape-pair occurrence scan is
exactly the canonical pair-local linear crossing count. -/
theorem routeShapePairCrossingCount_descriptorPairTokens
    (shapes : RouteShape × RouteShape)
    (pair : RouteDescriptor × RouteDescriptor)
    (firstMatches : shapes.1.Matches pair.1)
    (secondMatches : shapes.2.Matches pair.2) :
    routeShapePairCrossingCount (descriptorPairTokens pair) shapes =
      routeDescriptorPairLinearCrossingCountAtPeriod pair.1.gridSize pair := by
  unfold routeShapePairCrossingCount
    routeDescriptorPairLinearCrossingCountAtPeriod
  change List.filteredProductCount _ _ _ =
    List.filteredProductCount _
      (descriptorAt pair .first).selfIndexedNeighborOccurrences
      (descriptorAt pair .second).selfIndexedNeighborOccurrences
  rw [← shapes.1.map_evalPair_occurrences .first pair firstMatches,
    ← shapes.2.map_evalPair_occurrences .second pair secondMatches]
  rw [List.filteredProductCount_map]
  have predicateEq :
      (fun occurrences : Occurrence × Occurrence =>
        (crossingPredicate occurrences.1 occurrences.2).evalTokens
          (descriptorPairTokens pair)) =
        (fun occurrences : Occurrence × Occurrence =>
          canonicalOrientedOccurrencePairLinearAtPeriod pair.1.gridSize
            (occurrences.1.evalPair .first pair,
              occurrences.2.evalPair .second pair)) := by
    funext occurrencePair
    exact evalTokens_crossingPredicate
      occurrencePair.1 occurrencePair.2 pair
  rw [predicateEq]

/-- The guarded contribution of the unique matching shape pair is the exact
canonical pair-local linear crossing count. -/
theorem guardedRouteShapePairCrossingCount_descriptorPairTokens
    (shapes : RouteShape × RouteShape)
    (pair : RouteDescriptor × RouteDescriptor)
    (firstMatches : shapes.1.Matches pair.1)
    (secondMatches : shapes.2.Matches pair.2) :
    guardedRouteShapePairCrossingCount (descriptorPairTokens pair) shapes =
      routeDescriptorPairLinearCrossingCountAtPeriod pair.1.gridSize pair := by
  unfold guardedRouteShapePairCrossingCount
  rw [show routeShapePairEnabled (descriptorPairTokens pair) shapes = true by
    exact (routeShapePairEnabled_descriptorPairTokens shapes pair).2
      ⟨firstMatches, secondMatches⟩]
  exact routeShapePairCrossingCount_descriptorPairTokens
    shapes pair firstMatches secondMatches

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes
