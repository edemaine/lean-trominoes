/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingSourceKeyRecipeData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairSourceKeyRecipePairData

/-! # Explicit crossing source-key recipe pairs -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags
open RouteDescriptorPairSourceKeyRecipePairs

def occurrencePairCrossingSourceKeyShiftRecipePairBlock
    (occurrences : Occurrence × Occurrence) (shift : Cell) :
    List RecipePair :=
  let second := occurrences.2.sourceKeyRecipeAtShift .second shift
  [(occurrences.1.taggedSourceKeyRecipeAtShift .first shift .left, second),
    (occurrences.1.taggedSourceKeyRecipeAtShift .first shift .right, second),
    (occurrences.1.taggedSourceKeyRecipeAtShift .first shift .top, second),
    (occurrences.1.taggedSourceKeyRecipeAtShift .first shift .bottom, second)]

def occurrencePairCrossingSourceKeyRecipePairBlock
    (occurrences : Occurrence × Occurrence) : List RecipePair :=
  carrierCrossingRetentionShifts.flatMap
    (occurrencePairCrossingSourceKeyShiftRecipePairBlock occurrences)

end RouteDescriptorPairAffine

namespace RouteDescriptorOccurrenceSlotCrossing

open RouteDescriptorPairAffine
open RouteDescriptorPairSourceKeyRecipePairs

def Slot.sourceKeyRecipePairBlock (slot : Slot) : List RecipePair :=
  occurrencePairCrossingSourceKeyRecipePairBlock slot.occurrences

def crossingSourceKeyRecipePairBlocks : List (List RecipePair) :=
  crossingSlots.map Slot.sourceKeyRecipePairBlock

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
