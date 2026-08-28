/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingShiftSlotData
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairCanonicalShiftData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingShapePairSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCrossingCompiler
import LeanTrominoes.DelimitedBinaryWordOccurrenceSlotTags
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotFieldValueSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotPairProjectionSemantics
import LeanTrominoes.ListFlatMapUnique
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairPaddedOccurrenceTemplateSlotSemantics

/-! # Semantics of fixed common-shift crossing slots -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags

@[simp] theorem Occurrence.subtractShift_evalPair
    (occurrence : Occurrence) (shift : Cell) (side : Side)
    (pair : RouteDescriptor × RouteDescriptor) :
    (occurrence.subtractShift shift).evalPair side pair =
      ((occurrence.evalPair side pair).1,
        Cell.sub (occurrence.evalPair side pair).2 shift) := by
  rfl

/-- Evaluating two shifted affine templates is exactly semantic common-shift
subtraction on their evaluated occurrence pair. -/
theorem occurrencePairSubtractShift_evalPair
    (occurrences : Occurrence × Occurrence) (shift : Cell)
    (pair : RouteDescriptor × RouteDescriptor) :
    let shifted := occurrencePairSubtractShift occurrences shift
    (shifted.1.evalPair .first pair,
        shifted.2.evalPair .second pair) =
      LeanTrominoes.PeriodicOrthocrossing.occurrencePairSubtractShift
        (occurrences.1.evalPair .first pair,
          occurrences.2.evalPair .second pair) shift := by
  rfl

end RouteDescriptorPairAffine

namespace RouteDescriptorOccurrenceSlotCrossing

open RouteDescriptorOccurrenceSlotBinaryWords
open RouteDescriptorOccurrenceSlotPairFieldTags
open RouteDescriptorPairAffine

@[simp] theorem Slot.canonicalShift_firstSlot
    (slot : Slot) (shapes : RouteShape × RouteShape) (shift : Cell) :
    (slot.canonicalShift shapes shift).firstSlot = slot.firstSlot := by
  rfl

@[simp] theorem Slot.canonicalShift_secondSlot
    (slot : Slot) (shapes : RouteShape × RouteShape) (shift : Cell) :
    (slot.canonicalShift shapes shift).secondSlot = slot.secondSlot := by
  rfl

/-- Slot-index filtering is unaffected by shifting the affine occurrence
templates. -/
theorem filter_routeShapePairCanonicalShiftCrossingSlots_indices
    (shift : Cell) (shapes : RouteShape × RouteShape)
    (pair : TaggedDescriptor × TaggedDescriptor) :
    (routeShapePairCanonicalShiftCrossingSlots shift shapes).filter
        (fun slot =>
          decide (pair.1.2.val = slot.firstSlot) &&
            decide (pair.2.2.val = slot.secondSlot)) =
      match
        shapes.1.paddedOccurrenceAtSlot .first pair.1.2,
        shapes.2.paddedOccurrenceAtSlot .second pair.2.2
      with
      | some first, some second =>
          [Slot.canonicalShift shapes shift
            { descriptorPredicate :=
                guardedCrossingPredicate shapes (first, second)
              occurrences := (first, second)
              firstSlot := pair.1.2.val
              secondSlot := pair.2.2.val }]
      | _, _ => [] := by
  unfold routeShapePairCanonicalShiftCrossingSlots
  rw [List.filter_map]
  have predicateEq :
      ((fun shifted : Slot =>
        decide (pair.1.2.val = shifted.firstSlot) &&
          decide (pair.2.2.val = shifted.secondSlot)) ∘
        Slot.canonicalShift shapes shift) =
      (fun slot : Slot =>
        decide (pair.1.2.val = slot.firstSlot) &&
          decide (pair.2.2.val = slot.secondSlot)) := by
    funext slot
    rfl
  rw [predicateEq,
    filter_routeShapePairCrossingSlots_indices shapes pair]
  cases firstLookup :
      shapes.1.paddedOccurrenceAtSlot .first pair.1.2 with
  | none => rfl
  | some first =>
      cases secondLookup :
          shapes.2.paddedOccurrenceAtSlot .second pair.2.2 with
      | none => rfl
      | some second => rfl

/-- For matching descriptors, one shift block retains its unique runtime
slot exactly when the shifted occurrence pair is a canonical crossing. -/
theorem filter_routeShapePairCanonicalShiftCrossingSlots_evalTokens_of_matches
    (shift : Cell) (shapes : RouteShape × RouteShape)
    (pair : TaggedDescriptor × TaggedDescriptor)
    (firstMatches : shapes.1.Matches pair.1.1)
    (secondMatches : shapes.2.Matches pair.2.1) :
    (routeShapePairCanonicalShiftCrossingSlots shift shapes).filter
        (fun slot => slot.evalTokens (descriptorSlotPairTokens pair)) =
      match
        shapes.1.paddedOccurrenceAtSlot .first pair.1.2,
        shapes.2.paddedOccurrenceAtSlot .second pair.2.2
      with
      | some first, some second =>
          let original : Slot :=
            { descriptorPredicate :=
                guardedCrossingPredicate shapes (first, second)
              occurrences := (first, second)
              firstSlot := pair.1.2.val
              secondSlot := pair.2.2.val }
          let shifted := original.canonicalShift shapes shift
          if canonicalOrientedOccurrencePairLinearAtPeriod
              pair.1.1.gridSize
              (shifted.occurrences.1.evalPair .first
                  (pair.1.1, pair.2.1),
                shifted.occurrences.2.evalPair .second
                  (pair.1.1, pair.2.1)) then
            [shifted]
          else
            []
      | _, _ => [] := by
  have filterEq :
      (routeShapePairCanonicalShiftCrossingSlots shift shapes).filter
          (fun slot => slot.evalTokens (descriptorSlotPairTokens pair)) =
        ((routeShapePairCanonicalShiftCrossingSlots shift shapes).filter
          (fun slot =>
            decide (pair.1.2.val = slot.firstSlot) &&
              decide (pair.2.2.val = slot.secondSlot))).filter fun slot =>
                slot.descriptorPredicate.evalTokens
                  (descriptorTokens (descriptorSlotPairTokens pair)) := by
    rw [List.filter_filter]
    apply congrArg
      (fun predicate : Slot → Bool =>
        (routeShapePairCanonicalShiftCrossingSlots shift shapes).filter
          predicate)
    funext slot
    unfold Slot.evalTokens
    have firstSlotValue :
        slotValue (descriptorSlotPairTokens pair)
            RouteDescriptorPairFieldTags.Side.first =
          pair.1.2.val := by
      exact slotValue_descriptorSlotPairTokens pair
        RouteDescriptorPairFieldTags.Side.first
    have secondSlotValue :
        slotValue (descriptorSlotPairTokens pair)
            RouteDescriptorPairFieldTags.Side.second =
          pair.2.2.val := by
      exact slotValue_descriptorSlotPairTokens pair
        RouteDescriptorPairFieldTags.Side.second
    rw [firstSlotValue, secondSlotValue]
    simp only [Bool.and_assoc, Bool.and_comm, Bool.and_left_comm]
  rw [filterEq,
    filter_routeShapePairCanonicalShiftCrossingSlots_indices]
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
          simp only [Slot.canonicalShift]
          rw [RouteDescriptorPairAffine.guardedCrossingPredicate_evalTokens,
            descriptorTokens_descriptorSlotPairTokens,
            enabled, Bool.true_and]
          rw [evalTokens_crossingPredicate]

/-- A nonmatching route-shape pair contributes no active slot at any proposed
common shift. -/
theorem filter_routeShapePairCanonicalShiftCrossingSlots_evalTokens_eq_nil_of_not_matches
    (shift : Cell) (shapes : RouteShape × RouteShape)
    (pair : TaggedDescriptor × TaggedDescriptor)
    (notMatches :
      ¬(shapes.1.Matches pair.1.1 ∧ shapes.2.Matches pair.2.1)) :
    (routeShapePairCanonicalShiftCrossingSlots shift shapes).filter
        (fun slot => slot.evalTokens (descriptorSlotPairTokens pair)) = [] := by
  have enabledFalse :
      routeShapePairEnabled
          (RouteDescriptorPairFieldTags.descriptorPairTokens
            (pair.1.1, pair.2.1)) shapes = false := by
    cases enabled : routeShapePairEnabled
        (RouteDescriptorPairFieldTags.descriptorPairTokens
          (pair.1.1, pair.2.1)) shapes with
    | false => rfl
    | true =>
        exact False.elim (notMatches
          ((routeShapePairEnabled_descriptorPairTokens
            shapes (pair.1.1, pair.2.1)).1 enabled))
  apply List.filter_eq_nil_iff.mpr
  intro slot slotMember active
  unfold routeShapePairCanonicalShiftCrossingSlots at slotMember
  rcases List.mem_map.mp slotMember with
    ⟨original, _originalMember, slotEq⟩
  subst slot
  unfold Slot.evalTokens Slot.canonicalShift at active
  rw [descriptorTokens_descriptorSlotPairTokens,
    RouteDescriptorPairAffine.guardedCrossingPredicate_evalTokens,
    enabledFalse] at active
  simp at active

/-- At one proposed common shift, the full fixed shape scan keeps exactly the
block belonging to the two matching local shapes. -/
theorem filter_canonicalCrossingSlotsAtShift_eq_of_matches
    (shift : Cell) (firstShape secondShape : RouteShape)
    (pair : TaggedDescriptor × TaggedDescriptor)
    (firstMatches : firstShape.Matches pair.1.1)
    (secondMatches : secondShape.Matches pair.2.1) :
    (canonicalCrossingSlotsAtShift shift).filter
        (fun slot => slot.evalTokens (descriptorSlotPairTokens pair)) =
      (routeShapePairCanonicalShiftCrossingSlots shift
        (firstShape, secondShape)).filter fun slot =>
          slot.evalTokens (descriptorSlotPairTokens pair) := by
  unfold canonicalCrossingSlotsAtShift
  rw [List.filter_flatMap]
  rw [List.flatMap_eq_selected_of_unique
    (allRouteShapes ×ˢ allRouteShapes)
    (fun shapes =>
      (routeShapePairCanonicalShiftCrossingSlots shift shapes).filter
        fun slot => slot.evalTokens (descriptorSlotPairTokens pair))
    (firstShape, secondShape)
    (allRouteShapes_nodup.product allRouteShapes_nodup)
    (List.mem_product.mpr
      ⟨mem_allRouteShapes firstShape, mem_allRouteShapes secondShape⟩)]
  intro shapes _shapesMember shapesNe
  apply
    filter_routeShapePairCanonicalShiftCrossingSlots_evalTokens_eq_nil_of_not_matches
  intro shapeMatches
  apply shapesNe
  apply Prod.ext
  · exact RouteShape.eq_of_matches shapeMatches.1 firstMatches
  · exact RouteShape.eq_of_matches shapeMatches.2 secondMatches

/-- Erasing affine metadata from one accepted shift block gives exactly the
optional shifted canonical pair at the two runtime occurrence slots. -/
theorem map_filter_canonicalCrossingSlotsAtShift_eq_candidate_of_matches
    (shift : Cell) (firstShape secondShape : RouteShape)
    (pair : TaggedDescriptor × TaggedDescriptor)
    (firstMatches : firstShape.Matches pair.1.1)
    (secondMatches : secondShape.Matches pair.2.1) :
    ((canonicalCrossingSlotsAtShift shift).filter fun slot =>
        slot.evalTokens (descriptorSlotPairTokens pair)).map (fun slot =>
          (slot.occurrences.1.evalPair .first (pair.1.1, pair.2.1),
            slot.occurrences.2.evalPair .second
              (pair.1.1, pair.2.1))) =
      (canonicalShiftCandidateAtPeriod
        pair.1.1.gridSize pair shift).toList := by
  rw [filter_canonicalCrossingSlotsAtShift_eq_of_matches
      shift firstShape secondShape pair firstMatches secondMatches,
    filter_routeShapePairCanonicalShiftCrossingSlots_evalTokens_of_matches
      shift (firstShape, secondShape) pair firstMatches secondMatches]
  cases firstLookup :
      firstShape.paddedOccurrenceAtSlot .first pair.1.2 with
  | none =>
      have firstEval := firstShape.paddedOccurrenceAtSlot_evalPair
        .first (pair.1.1, pair.2.1) firstMatches pair.1.2
      rw [firstLookup] at firstEval
      have firstSemantic : occurrenceAtSlot pair.1 = none := by
        simpa [occurrenceAtSlot, descriptorAt] using firstEval.symm
      rw [canonicalShiftCandidateAtPeriod, firstSemantic]
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
          rw [canonicalShiftCandidateAtPeriod,
            firstSemantic, secondSemantic]
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
          rw [canonicalShiftCandidateAtPeriod,
            firstSemantic, secondSemantic]
          simp only [Option.toList,
            LeanTrominoes.PeriodicOrthocrossing.occurrencePairCanonicalShiftCandidateAtPeriod]
          rw [canonicalOrientedOccurrencePairAtPeriod_eq_linear]
          have firstShiftedEval := Occurrence.subtractShift_evalPair
            first shift RouteDescriptorPairFieldTags.Side.first
              (pair.1.1, pair.2.1)
          have secondShiftedEval := Occurrence.subtractShift_evalPair
            second shift RouteDescriptorPairFieldTags.Side.second
              (pair.1.1, pair.2.1)
          unfold LeanTrominoes.PeriodicOrthocrossing.occurrencePairSubtractShift
          by_cases accepted :
              canonicalOrientedOccurrencePairLinearAtPeriod
                pair.1.1.gridSize
                (((first.evalPair .first (pair.1.1, pair.2.1)).1,
                    Cell.sub
                      (first.evalPair .first (pair.1.1, pair.2.1)).2 shift),
                  ((second.evalPair .second (pair.1.1, pair.2.1)).1,
                    Cell.sub
                      (second.evalPair .second
                        (pair.1.1, pair.2.1)).2 shift)) = true
          · simp [Slot.canonicalShift,
              RouteDescriptorPairAffine.occurrencePairSubtractShift,
              firstShiftedEval, secondShiftedEval, accepted]
          · have rejected := Bool.eq_false_of_not_eq_true accepted
            simp [Slot.canonicalShift,
              RouteDescriptorPairAffine.occurrencePairSubtractShift,
              firstShiftedEval, secondShiftedEval, rejected]

/-- Erasing affine metadata from the complete shift-major schedule gives the
twenty-five optional semantic shift candidates in the same order. -/
theorem map_filter_canonicalCrossingShiftSlots_eq_candidates_of_matches
    (firstShape secondShape : RouteShape)
    (pair : TaggedDescriptor × TaggedDescriptor)
    (firstMatches : firstShape.Matches pair.1.1)
    (secondMatches : secondShape.Matches pair.2.1) :
    (canonicalCrossingShiftSlots.filter fun slot =>
        slot.evalTokens (descriptorSlotPairTokens pair)).map (fun slot =>
          (slot.occurrences.1.evalPair .first (pair.1.1, pair.2.1),
            slot.occurrences.2.evalPair .second
              (pair.1.1, pair.2.1))) =
      carrierCrossingRetentionShifts.filterMap
        (canonicalShiftCandidateAtPeriod pair.1.1.gridSize pair) := by
  unfold canonicalCrossingShiftSlots
  rw [List.filter_flatMap, List.map_flatMap,
    List.filterMap_eq_flatMap_toList]
  apply List.flatMap_congr
  intro shift _shiftMember
  exact
    map_filter_canonicalCrossingSlotsAtShift_eq_candidate_of_matches
      shift firstShape secondShape pair firstMatches secondMatches

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
