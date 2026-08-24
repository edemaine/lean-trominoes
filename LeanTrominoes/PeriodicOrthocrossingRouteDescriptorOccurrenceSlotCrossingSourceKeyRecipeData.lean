/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeSourceKeyTagData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingPredicateData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairCarrierKeyWordRecipeData

/-! # Doubled source-key recipes for padded crossing-boundary nodes -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open CarrierNodeSourceKeys
open RouteDescriptorPairCarrierKeyWordRecipes
open RouteDescriptorPairFieldTags

def Occurrence.taggedSourceKeyRecipeAtShift
    (occurrence : Occurrence) (side : Side) (shift : Cell)
    (boundarySide : CrossingSide) : Recipe :=
  { side := side
    segmentIndex :=
      8 * occurrence.segmentIndex + crossingSideTag boundarySide
    translate := Cell.add occurrence.translate shift
    supported := true }

def Occurrence.sourceKeyRecipeAtShift
    (occurrence : Occurrence) (side : Side) (shift : Cell) : Recipe :=
  { side := side
    segmentIndex := occurrence.segmentIndex
    translate := Cell.add occurrence.translate shift
    supported := true }

/-- Each boundary slot contributes its tagged first occurrence followed by
the unmodified second occurrence. -/
def occurrencePairCrossingSourceKeyShiftRecipeBlock
    (occurrences : Occurrence × Occurrence) (shift : Cell) : List Recipe :=
  let second := occurrences.2.sourceKeyRecipeAtShift .second shift
  [occurrences.1.taggedSourceKeyRecipeAtShift .first shift .left, second,
    occurrences.1.taggedSourceKeyRecipeAtShift .first shift .right, second,
    occurrences.1.taggedSourceKeyRecipeAtShift .first shift .top, second,
    occurrences.1.taggedSourceKeyRecipeAtShift .first shift .bottom, second]

def occurrencePairCrossingSourceKeyRecipeBlock
    (occurrences : Occurrence × Occurrence) : List Recipe :=
  carrierCrossingRetentionShifts.flatMap
    (occurrencePairCrossingSourceKeyShiftRecipeBlock occurrences)

end RouteDescriptorPairAffine

namespace RouteDescriptorOccurrenceSlotCrossing

open RouteDescriptorPairAffine
open RouteDescriptorPairCarrierKeyWordRecipes

def Slot.sourceKeyRecipeBlock (slot : Slot) : List Recipe :=
  occurrencePairCrossingSourceKeyRecipeBlock slot.occurrences

/-- Complete doubled recipe family aligned with the slot-major crossing
activation word. -/
def crossingSourceKeyRecipeBlocks : List (List Recipe) :=
  crossingSlots.map Slot.sourceKeyRecipeBlock

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing

end
