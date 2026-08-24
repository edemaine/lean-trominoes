/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingPredicateData

/-! # Alignment of slot-guarded and affine crossing scans -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open RouteDescriptorPairAffine

/-- Erasing the indices from a product of indexed lists recovers the original
row-major product. -/
theorem product_zipIdx_map_values
    (firsts : List α) (seconds : List β) :
    (firsts.zipIdx ×ˢ seconds.zipIdx).map (fun pair =>
        (pair.1.1, pair.2.1)) =
      firsts ×ˢ seconds := by
  calc
    (firsts.zipIdx ×ˢ seconds.zipIdx).map (fun pair =>
        (pair.1.1, pair.2.1)) =
      (firsts.zipIdx.map Prod.fst ×ˢ
        seconds.zipIdx.map Prod.fst) := by
      symm
      exact
        RouteDescriptorOccurrenceSlotBinaryWords.product_map_map
          firsts.zipIdx seconds.zipIdx Prod.fst Prod.fst
    _ = firsts ×ˢ seconds := by
      rw [List.zipIdx_map_fst, List.zipIdx_map_fst]

/-- Erasing slot metadata from one shape-pair scan gives exactly the existing
affine predicate list. -/
theorem routeShapePairCrossingSlots_map_descriptorPredicate
    (shapes : RouteShape × RouteShape) :
    (routeShapePairCrossingSlots shapes).map
        Slot.descriptorPredicate =
      routeShapePairCrossingPredicates shapes := by
  unfold routeShapePairCrossingSlots
    routeShapePairCrossingPredicates
  rw [List.map_map]
  change ((shapes.1.occurrences .first).zipIdx ×ˢ
      (shapes.2.occurrences .second).zipIdx).map
        (fun pair => guardedCrossingPredicate shapes
          (pair.1.1, pair.2.1)) = _
  calc
    _ = (((shapes.1.occurrences .first).zipIdx ×ˢ
          (shapes.2.occurrences .second).zipIdx).map fun pair =>
            (pair.1.1, pair.2.1)).map
          (guardedCrossingPredicate shapes) := by
        simp only [List.map_map, Function.comp_def]
    _ = _ := congrArg
      (List.map (guardedCrossingPredicate shapes))
      (product_zipIdx_map_values
        (shapes.1.occurrences .first)
        (shapes.2.occurrences .second))

/-- The complete slot scan is position-for-position aligned with the existing
compact affine crossing scan. -/
theorem crossingSlots_map_descriptorPredicate :
    crossingSlots.map Slot.descriptorPredicate =
      affineCrossingPredicates := by
  unfold crossingSlots affineCrossingPredicates
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro shapes _
  exact routeShapePairCrossingSlots_map_descriptorPredicate shapes

@[simp] theorem crossingSlots_length :
    crossingSlots.length = affineCrossingPredicates.length := by
  rw [← crossingSlots_map_descriptorPredicate, List.length_map]

/-- Slot metadata does not change the candidate carrier-key template block
aligned with any one shape-pair occurrence scan. -/
theorem routeShapePairCrossingSlots_map_carrierKeyTemplateBlock
    (pair : RouteDescriptor × RouteDescriptor)
    (shapes : RouteShape × RouteShape) :
    (routeShapePairCrossingSlots shapes).map
        (Slot.carrierKeyTemplateBlock pair) =
      routeShapePairCrossingCarrierKeyTemplateBlocks pair shapes := by
  unfold routeShapePairCrossingSlots
    routeShapePairCrossingCarrierKeyTemplateBlocks
    Slot.carrierKeyTemplateBlock
  rw [List.map_map]
  change ((shapes.1.occurrences .first).zipIdx ×ˢ
      (shapes.2.occurrences .second).zipIdx).map
        (fun tagged => occurrencePairCrossingCarrierKeyTemplateBlock pair
          (tagged.1.1, tagged.2.1)) = _
  calc
    _ = (((shapes.1.occurrences .first).zipIdx ×ˢ
          (shapes.2.occurrences .second).zipIdx).map fun tagged =>
            (tagged.1.1, tagged.2.1)).map
          (occurrencePairCrossingCarrierKeyTemplateBlock pair) := by
        simp only [List.map_map, Function.comp_def]
    _ = _ := congrArg
      (List.map (occurrencePairCrossingCarrierKeyTemplateBlock pair))
      (product_zipIdx_map_values
        (shapes.1.occurrences .first)
        (shapes.2.occurrences .second))

/-- The complete slot scan carries exactly the old aligned template-block
list, while its runtime order is governed by the expanded slot-pair stream. -/
theorem crossingCarrierKeyTemplateBlocks_eq
    (pair : RouteDescriptor × RouteDescriptor) :
    crossingCarrierKeyTemplateBlocks pair =
      RouteDescriptorPairAffine.crossingCarrierKeyTemplateBlocks pair := by
  unfold crossingCarrierKeyTemplateBlocks crossingSlots
    RouteDescriptorPairAffine.crossingCarrierKeyTemplateBlocks
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro shapes _
  exact routeShapePairCrossingSlots_map_carrierKeyTemplateBlock pair shapes

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
