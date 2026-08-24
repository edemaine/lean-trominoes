/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPaddedOccurrenceSlots
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairOccurrenceTemplateSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairPaddedOccurrenceTemplateSlots

/-! # Semantics of padded affine occurrence-template slots -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags

/-- Evaluating every padded affine occurrence-template slot gives exactly
the padded semantic occurrence slots of the selected descriptor. -/
theorem RouteShape.map_paddedOccurrences
    (shape : RouteShape) (side : Side)
    (pair : RouteDescriptor × RouteDescriptor)
    (shapeMatches : shape.Matches (descriptorAt pair side)) :
    (shape.paddedOccurrences side).map
        (Option.map fun occurrence => occurrence.evalPair side pair) =
      (descriptorAt pair side).paddedNeighborOccurrenceSlots := by
  unfold RouteShape.paddedOccurrences
    RouteDescriptor.paddedNeighborOccurrenceSlots
  rw [← shape.map_evalPair_occurrences side pair shapeMatches]
  simp only [List.map_append, List.map_map, List.map_replicate,
    Option.map_none, List.length_map]
  congr 1

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
