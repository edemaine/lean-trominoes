/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingSourceKeyRecipeData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairSourceKeyRecipePairData

/-! # Canonical-left source-key recipes for crossing slots -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairCarrierKeyWordRecipes

/-- The two source-key components of the canonical left boundary represented
by one canonical occurrence pair. -/
def occurrencePairCanonicalCrossingLeftSourceKeyRecipeBlock
    (occurrences : Occurrence × Occurrence) : List Recipe :=
  [occurrences.1.taggedSourceKeyRecipeAtShift .first (0, 0) .left,
    occurrences.2.sourceKeyRecipeAtShift .second (0, 0)]

/-- The same two components grouped as one source-key recipe pair. -/
def occurrencePairCanonicalCrossingLeftSourceKeyRecipePairBlock
    (occurrences : Occurrence × Occurrence) :
    List RouteDescriptorPairSourceKeyRecipePairs.RecipePair :=
  [(occurrences.1.taggedSourceKeyRecipeAtShift .first (0, 0) .left,
    occurrences.2.sourceKeyRecipeAtShift .second (0, 0))]

end RouteDescriptorPairAffine

namespace RouteDescriptorOccurrenceSlotCrossing

open RouteDescriptorPairAffine
open RouteDescriptorPairCarrierKeyWordRecipes

/-- One canonical-left source pair aligned with a fixed crossing slot. -/
def Slot.canonicalLeftSourceKeyRecipeBlock (slot : Slot) : List Recipe :=
  occurrencePairCanonicalCrossingLeftSourceKeyRecipeBlock slot.occurrences

def Slot.canonicalLeftSourceKeyRecipePairBlock (slot : Slot) :
    List RouteDescriptorPairSourceKeyRecipePairs.RecipePair :=
  occurrencePairCanonicalCrossingLeftSourceKeyRecipePairBlock slot.occurrences

/-- Complete two-component recipe blocks aligned with `crossingSlots`. -/
def canonicalLeftSourceKeyRecipeBlocks : List (List Recipe) :=
  crossingSlots.map Slot.canonicalLeftSourceKeyRecipeBlock

def canonicalLeftSourceKeyRecipePairBlocks :
    List (List RouteDescriptorPairSourceKeyRecipePairs.RecipePair) :=
  crossingSlots.map Slot.canonicalLeftSourceKeyRecipePairBlock

/-- Guarded source-key components emitted from one tagged descriptor-slot
pair.  Exactly one two-word block is active for a genuine canonical crossing
pair. -/
def canonicalLeftSourceKeyGuardedWords
    (tokens : List RouteDescriptorOccurrenceSlotPairFieldTags.Token) :
    List (List Bool) :=
  RouteDescriptorPairCarrierKeyWordRecipes.words
    (RouteDescriptorOccurrenceSlotPairFieldTags.descriptorTokens tokens)
    (crossingActivations tokens) canonicalLeftSourceKeyRecipeBlocks

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing

end
