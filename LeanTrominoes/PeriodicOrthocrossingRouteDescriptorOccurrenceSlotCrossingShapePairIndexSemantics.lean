/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListProductZipIdxFilterAt
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingPredicateData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairPaddedOccurrenceTemplateSlots

/-! # Exact index selection inside one route-shape crossing scan -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open RouteDescriptorOccurrenceSlotBinaryWords
open RouteDescriptorPairAffine

/-- Selecting the two runtime indices from one shape-pair crossing scan gives
its unique affine occurrence-template pair when both indices are present. -/
theorem filter_routeShapePairCrossingSlots_indices
    (shapes : RouteShape × RouteShape)
    (pair : TaggedDescriptor × TaggedDescriptor) :
    (routeShapePairCrossingSlots shapes).filter (fun slot =>
      decide (pair.1.2.val = slot.firstSlot) &&
        decide (pair.2.2.val = slot.secondSlot)) =
      match
        shapes.1.paddedOccurrenceAtSlot .first pair.1.2,
        shapes.2.paddedOccurrenceAtSlot .second pair.2.2
      with
      | some first, some second =>
          [{ descriptorPredicate :=
                guardedCrossingPredicate shapes (first, second)
             occurrences := (first, second)
             firstSlot := pair.1.2.val
             secondSlot := pair.2.2.val }]
      | _, _ => [] := by
  unfold routeShapePairCrossingSlots
    RouteShape.paddedOccurrenceAtSlot
  rw [List.filter_map]
  change (((shapes.1.occurrences .first).zipIdx ×ˢ
      (shapes.2.occurrences .second).zipIdx).filter
        (((fun slot : Slot =>
            decide (pair.1.2.val = slot.firstSlot) &&
              decide (pair.2.2.val = slot.secondSlot))) ∘
          (fun tagged =>
            ({ descriptorPredicate := guardedCrossingPredicate shapes
                (tagged.1.1, tagged.2.1)
               occurrences := (tagged.1.1, tagged.2.1)
               firstSlot := tagged.1.2
               secondSlot := tagged.2.2 } : Slot)))).map
        (fun tagged : (Occurrence × Nat) × (Occurrence × Nat) =>
          ({ descriptorPredicate := guardedCrossingPredicate shapes
              (tagged.1.1, tagged.2.1)
             occurrences := (tagged.1.1, tagged.2.1)
             firstSlot := tagged.1.2
             secondSlot := tagged.2.2 } : Slot)) = _
  have predicateEq :
      ((fun slot : Slot =>
          decide (pair.1.2.val = slot.firstSlot) &&
            decide (pair.2.2.val = slot.secondSlot)) ∘
        (fun tagged : (Occurrence × Nat) × (Occurrence × Nat) =>
          ({ descriptorPredicate := guardedCrossingPredicate shapes
              (tagged.1.1, tagged.2.1)
             occurrences := (tagged.1.1, tagged.2.1)
             firstSlot := tagged.1.2
             secondSlot := tagged.2.2 } : Slot))) =
        (fun tagged : (Occurrence × Nat) × (Occurrence × Nat) =>
          decide (pair.1.2.val = tagged.1.2) &&
            decide (pair.2.2.val = tagged.2.2)) := by
    rfl
  have filteredEq := congrArg
    (fun predicate =>
      (((shapes.1.occurrences .first).zipIdx ×ˢ
        (shapes.2.occurrences .second).zipIdx).filter predicate))
    predicateEq
  rw [filteredEq]
  rw [List.filter_product_zipIdx_eq_indices]
  cases (shapes.1.occurrences .first)[pair.1.2.val]? <;>
    cases (shapes.2.occurrences .second)[pair.2.2.val]? <;> rfl

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
