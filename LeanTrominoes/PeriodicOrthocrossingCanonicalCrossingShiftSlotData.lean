/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierOrbitOwnership
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingLeftSourceKeyRecipeData
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairCanonicalShiftData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotData

/-! # Fixed common-shift crossing slots -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

/-- Subtract one fixed common lattice shift from an affine occurrence
template. -/
def Occurrence.subtractShift
    (occurrence : Occurrence) (shift : Cell) : Occurrence where
  segmentIndex := occurrence.segmentIndex
  segment := occurrence.segment
  translate := Cell.sub occurrence.translate shift

/-- Subtract the same fixed shift from both templates of an ordered affine
occurrence pair. -/
def occurrencePairSubtractShift
    (occurrences : Occurrence × Occurrence) (shift : Cell) :
    Occurrence × Occurrence :=
  (occurrences.1.subtractShift shift,
    occurrences.2.subtractShift shift)

end RouteDescriptorPairAffine

namespace RouteDescriptorOccurrenceSlotCrossing

open RouteDescriptorPairAffine
open RouteDescriptorPairCarrierKeyWordRecipes

/-- Shift a slot's affine occurrences and rebuild its descriptor predicate,
while retaining the two physical runtime slot guards. -/
def Slot.canonicalShift
    (shapes : RouteShape × RouteShape) (shift : Cell)
    (slot : Slot) : Slot :=
  let shifted := RouteDescriptorPairAffine.occurrencePairSubtractShift
    slot.occurrences shift
  { descriptorPredicate := guardedCrossingPredicate shapes shifted
    occurrences := shifted
    firstSlot := slot.firstSlot
    secondSlot := slot.secondSlot }

/-- One route-shape pair's physical slot guards, with its affine occurrence
templates shifted by a proposed canonicalizing quotient. -/
def routeShapePairCanonicalShiftCrossingSlots
    (shift : Cell) (shapes : RouteShape × RouteShape) : List Slot :=
  (routeShapePairCrossingSlots shapes).map
    (Slot.canonicalShift shapes shift)

/-- Every shape-pair slot at one fixed proposed common shift. -/
def canonicalCrossingSlotsAtShift (shift : Cell) : List Slot :=
  (allRouteShapes ×ˢ allRouteShapes).flatMap
    (routeShapePairCanonicalShiftCrossingSlots shift)

/-- Complete shift-major schedule: twenty-five common shifts, each followed
by the ordinary shape/occurrence slot order. -/
def canonicalCrossingShiftSlots : List Slot :=
  carrierCrossingRetentionShifts.flatMap canonicalCrossingSlotsAtShift

/-- Optional shifted canonical pair represented by one physical runtime slot
pair and one proposed common quotient. -/
def canonicalShiftCandidateAtPeriod
    (period : Nat)
    (pair : RouteDescriptorOccurrenceSlotBinaryWords.TaggedDescriptor ×
      RouteDescriptorOccurrenceSlotBinaryWords.TaggedDescriptor)
    (shift : Cell) :
    Option ((IndexedGridSegment × Cell) ×
      (IndexedGridSegment × Cell)) :=
  match
    RouteDescriptorOccurrenceSlotBinaryWords.occurrenceAtSlot pair.1,
    RouteDescriptorOccurrenceSlotBinaryWords.occurrenceAtSlot pair.2
  with
  | some first, some second =>
      LeanTrominoes.PeriodicOrthocrossing.occurrencePairCanonicalShiftCandidateAtPeriod
        period (first, second) shift
  | _, _ => none

/-- One canonical-left source-key recipe block per shifted crossing slot. -/
def canonicalCrossingShiftLeftSourceKeyRecipeBlocks :
    List (List Recipe) :=
  canonicalCrossingShiftSlots.map fun slot =>
    occurrencePairCanonicalCrossingLeftSourceKeyRecipeBlock slot.occurrences

/-- Paired-component form of the same shifted source-key recipes. -/
def canonicalCrossingShiftLeftSourceKeyRecipePairBlocks :
    List (List RouteDescriptorPairSourceKeyRecipePairs.RecipePair) :=
  canonicalCrossingShiftSlots.map fun slot =>
    occurrencePairCanonicalCrossingLeftSourceKeyRecipePairBlock
      slot.occurrences

/-- Guarded canonical-left source-key components emitted by the complete
shift-major slot schedule. -/
def canonicalCrossingShiftLeftSourceKeyGuardedWords
    (tokens : List RouteDescriptorOccurrenceSlotPairFieldTags.Token) :
    List (List Bool) :=
  RouteDescriptorPairCarrierKeyWordRecipes.words
    (RouteDescriptorOccurrenceSlotPairFieldTags.descriptorTokens tokens)
    (canonicalCrossingShiftSlots.map fun slot => slot.evalTokens tokens)
    canonicalCrossingShiftLeftSourceKeyRecipeBlocks

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
