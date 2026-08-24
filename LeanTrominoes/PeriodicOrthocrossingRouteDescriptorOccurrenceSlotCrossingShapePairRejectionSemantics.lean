/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingShapePairSemantics

/-! # Rejected route-shape slot crossing scans -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open RouteDescriptorOccurrenceSlotBinaryWords
open RouteDescriptorOccurrenceSlotPairFieldTags
open RouteDescriptorPairAffine

/-- A route-shape pair whose guards do not both match contributes no accepted
slot crossing. -/
theorem filter_routeShapePairCrossingSlots_evalTokens_eq_nil_of_not_matches
    (shapes : RouteShape × RouteShape)
    (pair : TaggedDescriptor × TaggedDescriptor)
    (notMatches :
      ¬(shapes.1.Matches pair.1.1 ∧ shapes.2.Matches pair.2.1)) :
    (routeShapePairCrossingSlots shapes).filter (fun slot =>
      slot.evalTokens (descriptorSlotPairTokens pair)) = [] := by
  have enabledFalse :
      routeShapePairEnabled
          (RouteDescriptorPairFieldTags.descriptorPairTokens
            (pair.1.1, pair.2.1)) shapes = false := by
    cases enabled :
        routeShapePairEnabled
          (RouteDescriptorPairFieldTags.descriptorPairTokens
            (pair.1.1, pair.2.1)) shapes with
    | false => rfl
    | true =>
        exact False.elim (notMatches
          ((routeShapePairEnabled_descriptorPairTokens
            shapes (pair.1.1, pair.2.1)).1 enabled))
  apply List.filter_eq_nil_iff.mpr
  intro slot slotMember active
  unfold routeShapePairCrossingSlots at slotMember
  rcases List.mem_map.mp slotMember with ⟨tagged, _taggedMember, rfl⟩
  unfold Slot.evalTokens at active
  rw [descriptorTokens_descriptorSlotPairTokens,
    guardedCrossingPredicate_evalTokens, enabledFalse] at active
  simp at active

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
