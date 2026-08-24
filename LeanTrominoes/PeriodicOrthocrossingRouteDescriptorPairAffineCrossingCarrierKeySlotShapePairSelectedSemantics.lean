/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListFilteredProductMap
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCrossingCarrierKeySlotShapePairSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCrossingScanLocalSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairLinearCrossingPairs

/-! # Selected shape-pair crossing carrier-key slot semantics -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags
open PaddedSupportedCandidateBlocks

/-- When both shape guards match, the active affine crossing-key slots are
the exact retained key expansion of the pair-local canonical crossings. -/
theorem routeShapePairCrossingCarrierKeyActiveValues_selected_eq
    (shapes : RouteShape × RouteShape)
    (pair : RouteDescriptor × RouteDescriptor)
    (firstMatches : shapes.1.Matches pair.1)
    (secondMatches : shapes.2.Matches pair.2) :
    activeValues
        ((routeShapePairCrossingPredicates shapes).map fun predicate =>
          predicate.evalTokens (descriptorPairTokens pair))
        (routeShapePairCrossingCarrierKeyTemplateBlocks pair shapes) =
      occurrencePairCarrierKeyScan
        (routeDescriptorPairLinearCrossingOccurrencePairsAtPeriod
          pair.1.gridSize pair) := by
  rw [routeShapePairCrossingCarrierKeyActiveValues_eq]
  unfold routeDescriptorPairLinearCrossingOccurrencePairsAtPeriod
    occurrencePairCarrierKeyScan
  have firstOccurrencesEq :
      (shapes.1.occurrences .first).map (fun occurrence =>
          occurrence.evalPair .first pair) =
        pair.1.selfIndexedNeighborOccurrences := by
    simpa [descriptorAt] using
      shapes.1.map_evalPair_occurrences .first pair firstMatches
  have secondOccurrencesEq :
      (shapes.2.occurrences .second).map (fun occurrence =>
          occurrence.evalPair .second pair) =
        pair.2.selfIndexedNeighborOccurrences := by
    simpa [descriptorAt] using
      shapes.2.map_evalPair_occurrences .second pair secondMatches
  rw [← firstOccurrencesEq, ← secondOccurrencesEq]
  rw [List.filteredProduct_map, List.flatMap_map]
  have enabled :
      routeShapePairEnabled (descriptorPairTokens pair) shapes = true :=
    (routeShapePairEnabled_descriptorPairTokens shapes pair).2
      ⟨firstMatches, secondMatches⟩
  have predicateEq :
      (fun occurrences : Occurrence × Occurrence =>
        (guardedCrossingPredicate shapes occurrences).evalTokens
          (descriptorPairTokens pair)) =
        (fun occurrences : Occurrence × Occurrence =>
          canonicalOrientedOccurrencePairLinearAtPeriod pair.1.gridSize
            (occurrences.1.evalPair .first pair,
              occurrences.2.evalPair .second pair)) := by
    funext occurrences
    rw [guardedCrossingPredicate_evalTokens, enabled, Bool.true_and]
    exact evalTokens_crossingPredicate
      occurrences.1 occurrences.2 pair
  rw [predicateEq]

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
