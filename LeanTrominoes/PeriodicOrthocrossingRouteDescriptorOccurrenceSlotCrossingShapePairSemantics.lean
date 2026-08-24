/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingShapePairIndexSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotFieldValueSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCrossingScanLocalSemantics

/-! # Exact semantics of one route-shape slot crossing scan -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open RouteDescriptorOccurrenceSlotBinaryWords
open RouteDescriptorOccurrenceSlotPairFieldTags
open RouteDescriptorPairAffine

/-- For the selected route-shape pair, the full slot predicate keeps its
unique indexed affine occurrence pair exactly when that pair is a canonical
oriented crossing. -/
theorem filter_routeShapePairCrossingSlots_evalTokens_of_matches
    (shapes : RouteShape × RouteShape)
    (pair : TaggedDescriptor × TaggedDescriptor)
    (firstMatches : shapes.1.Matches pair.1.1)
    (secondMatches : shapes.2.Matches pair.2.1) :
    (routeShapePairCrossingSlots shapes).filter (fun slot =>
      slot.evalTokens (descriptorSlotPairTokens pair)) =
      match
        shapes.1.paddedOccurrenceAtSlot .first pair.1.2,
        shapes.2.paddedOccurrenceAtSlot .second pair.2.2
      with
      | some first, some second =>
          if canonicalOrientedOccurrencePairLinearAtPeriod
              pair.1.1.gridSize
              (first.evalPair .first (pair.1.1, pair.2.1),
                second.evalPair .second (pair.1.1, pair.2.1))
          then
            [{ descriptorPredicate :=
                  guardedCrossingPredicate shapes (first, second)
               occurrences := (first, second)
               firstSlot := pair.1.2.val
               secondSlot := pair.2.2.val }]
          else []
      | _, _ => [] := by
  have filterEq :
      (routeShapePairCrossingSlots shapes).filter (fun slot =>
        slot.evalTokens (descriptorSlotPairTokens pair)) =
        ((routeShapePairCrossingSlots shapes).filter (fun slot =>
          decide (pair.1.2.val = slot.firstSlot) &&
            decide (pair.2.2.val = slot.secondSlot))).filter fun slot =>
              slot.descriptorPredicate.evalTokens
                (descriptorTokens (descriptorSlotPairTokens pair)) := by
    rw [List.filter_filter]
    apply congrArg
      (fun predicate : Slot → Bool =>
        (routeShapePairCrossingSlots shapes).filter predicate)
    funext slot
    unfold Slot.evalTokens
    rw [slotValue_descriptorSlotPairTokens,
      slotValue_descriptorSlotPairTokens]
    simp only
      [Bool.and_assoc, Bool.and_comm, Bool.and_left_comm]
  rw [filterEq, filter_routeShapePairCrossingSlots_indices]
  cases firstLookup :
      shapes.1.paddedOccurrenceAtSlot .first pair.1.2 with
  | none => rfl
  | some first =>
      cases secondLookup :
          shapes.2.paddedOccurrenceAtSlot .second pair.2.2 with
      | none => rfl
      | some second =>
          simp only [List.filter_cons, List.filter_nil]
          have enabled :
              routeShapePairEnabled
                  (RouteDescriptorPairFieldTags.descriptorPairTokens
                    (pair.1.1, pair.2.1)) shapes = true :=
            (routeShapePairEnabled_descriptorPairTokens
              shapes (pair.1.1, pair.2.1)).2
                ⟨firstMatches, secondMatches⟩
          rw [guardedCrossingPredicate_evalTokens,
            descriptorTokens_descriptorSlotPairTokens,
            enabled, Bool.true_and]
          rw [evalTokens_crossingPredicate]

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
