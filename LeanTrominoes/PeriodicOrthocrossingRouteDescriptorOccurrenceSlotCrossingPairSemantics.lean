/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListFlatMapUnique
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingShapePairRejectionSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairRouteShapeSelectionSemantics

/-! # Descriptor-slot-pair crossing selection semantics -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open RouteDescriptorOccurrenceSlotBinaryWords
open RouteDescriptorOccurrenceSlotPairFieldTags
open RouteDescriptorPairAffine

/-- Filtering the complete fixed crossing scan decomposes exactly into the
ordered route-shape-pair blocks. -/
theorem filter_crossingSlots_eq_shapePairs
    (pair : TaggedDescriptor × TaggedDescriptor) :
    crossingSlots.filter (fun slot =>
      slot.evalTokens (descriptorSlotPairTokens pair)) =
      (allRouteShapes ×ˢ allRouteShapes).flatMap fun shapes =>
        (routeShapePairCrossingSlots shapes).filter fun slot =>
          slot.evalTokens (descriptorSlotPairTokens pair) := by
  unfold crossingSlots
  rw [List.filter_flatMap]

/-- For locally selected descriptors, the complete fixed crossing scan keeps
exactly the contribution of their unique matching route-shape pair. -/
theorem filter_crossingSlots_eq_of_matches
    (firstShape secondShape : RouteShape)
    (pair : TaggedDescriptor × TaggedDescriptor)
    (firstMatches : firstShape.Matches pair.1.1)
    (secondMatches : secondShape.Matches pair.2.1) :
    crossingSlots.filter (fun slot =>
      slot.evalTokens (descriptorSlotPairTokens pair)) =
      (routeShapePairCrossingSlots
        (firstShape, secondShape)).filter fun slot =>
          slot.evalTokens (descriptorSlotPairTokens pair) := by
  rw [filter_crossingSlots_eq_shapePairs]
  rw [List.flatMap_eq_selected_of_unique
    (allRouteShapes ×ˢ allRouteShapes)
    (fun shapes =>
      (routeShapePairCrossingSlots shapes).filter fun slot =>
        slot.evalTokens (descriptorSlotPairTokens pair))
    (firstShape, secondShape)
    (allRouteShapes_nodup.product allRouteShapes_nodup)
    (List.mem_product.mpr
      ⟨mem_allRouteShapes firstShape, mem_allRouteShapes secondShape⟩)]
  intro shapes _shapesMember shapesNe
  apply
    filter_routeShapePairCrossingSlots_evalTokens_eq_nil_of_not_matches
  intro shapeMatches
  apply shapesNe
  apply Prod.ext
  · exact RouteShape.eq_of_matches shapeMatches.1 firstMatches
  · exact RouteShape.eq_of_matches shapeMatches.2 secondMatches

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
