/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingPredicateData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairCarrierKeyWordRecipeData

/-! # Word recipes for padded slot-major crossing carrier candidates -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairCarrierKeyWordRecipes
open RouteDescriptorPairFieldTags

/-- Fixed recipe of one affine occurrence after a retention shift. -/
def Occurrence.carrierKeyRecipeAtShift
    (occurrence : Occurrence) (side : Side) (shift : Cell) : Recipe :=
  { side := side
    segmentIndex := occurrence.segmentIndex
    translate := Cell.add occurrence.translate shift
    supported := occurrence.carrierKeyAtShiftSupported shift }

/-- Four crossing-boundary recipes for one retention shift: two copies from
the first occurrence followed by two from the second. -/
def occurrencePairCrossingCarrierKeyShiftRecipeBlock
    (occurrences : Occurrence × Occurrence) (shift : Cell) : List Recipe :=
  let first := occurrences.1.carrierKeyRecipeAtShift .first shift
  let second := occurrences.2.carrierKeyRecipeAtShift .second shift
  [first, first, second, second]

/-- Complete retained-shift recipe block for one fixed affine occurrence
pair. -/
def occurrencePairCrossingCarrierKeyRecipeBlock
    (occurrences : Occurrence × Occurrence) : List Recipe :=
  carrierCrossingRetentionShifts.flatMap
    (occurrencePairCrossingCarrierKeyShiftRecipeBlock occurrences)

end RouteDescriptorPairAffine

namespace RouteDescriptorOccurrenceSlotCrossing

open RouteDescriptorOccurrenceSlotPairFieldTags
open RouteDescriptorPairAffine
open RouteDescriptorPairCarrierKeyWordRecipes

/-- Carrier-key recipes associated with one fixed crossing slot. -/
def Slot.carrierKeyRecipeBlock (slot : Slot) : List Recipe :=
  occurrencePairCrossingCarrierKeyRecipeBlock slot.occurrences

/-- Complete recipe blocks aligned with the fixed slot-major crossing scan. -/
def crossingCarrierKeyRecipeBlocks : List (List Recipe) :=
  crossingSlots.map Slot.carrierKeyRecipeBlock

/-- Guarded crossing carrier-key words emitted from one twelve-field tagged
descriptor-slot pair block. -/
def crossingCarrierKeyGuardedWords
    (tokens : List RouteDescriptorOccurrenceSlotPairFieldTags.Token) :
    List (List Bool) :=
  RouteDescriptorPairCarrierKeyWordRecipes.words
    (descriptorTokens tokens) (crossingActivations tokens)
    crossingCarrierKeyRecipeBlocks

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
