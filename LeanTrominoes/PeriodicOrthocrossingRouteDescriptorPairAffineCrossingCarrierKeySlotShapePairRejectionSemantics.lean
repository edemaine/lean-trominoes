/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCrossingCarrierKeySlotShapePairSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCrossingScanLocalSemantics

/-! # Rejected shape-pair crossing carrier-key slots -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags
open PaddedSupportedCandidateBlocks

/-- A route-shape pair whose guards do not both match contributes no active
crossing carrier-key values. -/
theorem routeShapePairCrossingCarrierKeyActiveValues_eq_nil_of_not_matches
    (shapes : RouteShape × RouteShape)
    (pair : RouteDescriptor × RouteDescriptor)
    (notMatches :
      ¬(shapes.1.Matches pair.1 ∧ shapes.2.Matches pair.2)) :
    activeValues
        ((routeShapePairCrossingPredicates shapes).map fun predicate =>
          predicate.evalTokens (descriptorPairTokens pair))
        (routeShapePairCrossingCarrierKeyTemplateBlocks pair shapes) = [] := by
  rw [routeShapePairCrossingCarrierKeyActiveValues_eq]
  have enabledFalse :
      routeShapePairEnabled (descriptorPairTokens pair) shapes = false := by
    cases enabled :
        routeShapePairEnabled (descriptorPairTokens pair) shapes with
    | false => rfl
    | true =>
        exact False.elim (notMatches
          ((routeShapePairEnabled_descriptorPairTokens shapes pair).1
            enabled))
  simp [guardedCrossingPredicate_evalTokens, enabledFalse]

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
