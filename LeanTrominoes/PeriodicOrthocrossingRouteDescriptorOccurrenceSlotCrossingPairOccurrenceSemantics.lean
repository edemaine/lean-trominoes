/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListOptionalFilteredProduct
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingPairSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairPaddedOccurrenceTemplateSlotSemantics

/-! # Semantic occurrence selected by one descriptor-slot pair -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open RouteDescriptorOccurrenceSlotBinaryWords
open RouteDescriptorOccurrenceSlotPairFieldTags
open RouteDescriptorPairAffine

/-- Erasing affine metadata from the accepted fixed slot gives exactly the
optional canonical semantic crossing at the two runtime occurrence slots. -/
theorem map_filter_crossingSlots_eq_optionalFilteredPair_of_matches
    (firstShape secondShape : RouteShape)
    (pair : TaggedDescriptor × TaggedDescriptor)
    (firstMatches : firstShape.Matches pair.1.1)
    (secondMatches : secondShape.Matches pair.2.1) :
    (crossingSlots.filter (fun slot =>
        slot.evalTokens (descriptorSlotPairTokens pair))).map (fun slot =>
          (slot.occurrences.1.evalPair .first (pair.1.1, pair.2.1),
            slot.occurrences.2.evalPair .second
              (pair.1.1, pair.2.1))) =
      (List.optionalFilteredPair
        (canonicalOrientedOccurrencePairAtPeriod pair.1.1.gridSize)
        (occurrenceAtSlot pair.1) (occurrenceAtSlot pair.2)).toList := by
  rw [filter_crossingSlots_eq_of_matches
    firstShape secondShape pair firstMatches secondMatches]
  rw [filter_routeShapePairCrossingSlots_evalTokens_of_matches
    (firstShape, secondShape) pair firstMatches secondMatches]
  cases firstLookup :
      firstShape.paddedOccurrenceAtSlot .first pair.1.2 with
  | none =>
      have firstEval := firstShape.paddedOccurrenceAtSlot_evalPair
        .first (pair.1.1, pair.2.1) firstMatches pair.1.2
      rw [firstLookup] at firstEval
      have firstSemantic : occurrenceAtSlot pair.1 = none := by
        simpa [occurrenceAtSlot, descriptorAt] using firstEval.symm
      rw [firstSemantic]
      rfl
  | some first =>
      have firstEval := firstShape.paddedOccurrenceAtSlot_evalPair
        .first (pair.1.1, pair.2.1) firstMatches pair.1.2
      rw [firstLookup] at firstEval
      have firstSemantic :
          occurrenceAtSlot pair.1 =
            some (first.evalPair .first (pair.1.1, pair.2.1)) := by
        simpa [occurrenceAtSlot, descriptorAt] using firstEval.symm
      cases secondLookup :
          secondShape.paddedOccurrenceAtSlot .second pair.2.2 with
      | none =>
          have secondEval := secondShape.paddedOccurrenceAtSlot_evalPair
            .second (pair.1.1, pair.2.1) secondMatches pair.2.2
          rw [secondLookup] at secondEval
          have secondSemantic : occurrenceAtSlot pair.2 = none := by
            simpa [occurrenceAtSlot, descriptorAt] using secondEval.symm
          rw [firstSemantic, secondSemantic]
          rfl
      | some second =>
          have secondEval := secondShape.paddedOccurrenceAtSlot_evalPair
            .second (pair.1.1, pair.2.1) secondMatches pair.2.2
          rw [secondLookup] at secondEval
          have secondSemantic :
              occurrenceAtSlot pair.2 =
                some (second.evalPair .second
                  (pair.1.1, pair.2.1)) := by
            simpa [occurrenceAtSlot, descriptorAt] using secondEval.symm
          rw [firstSemantic, secondSemantic]
          simp only [List.optionalFilteredPair, Option.toList]
          rw [canonicalOrientedOccurrencePairAtPeriod_eq_linear]
          cases canonicalOrientedOccurrencePairLinearAtPeriod
              pair.1.1.gridSize
              (first.evalPair .first (pair.1.1, pair.2.1),
                second.evalPair .second (pair.1.1, pair.2.1)) <;> rfl

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
