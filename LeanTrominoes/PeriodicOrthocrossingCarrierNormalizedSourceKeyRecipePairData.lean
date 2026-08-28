/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateMap
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeNormalizedSourceKeyData
import LeanTrominoes.PeriodicOrthocrossingCarrierNormalizedSourceKeyRecipeData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingSourceKeyRecipePairData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalSourceKeyRecipePairData

/-! # Explicit normalized source-key recipe pairs -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierNormalizedSourceKeyRecipePairs

open PaddedSupportedLastRepresentativeEqualityRows
open RouteDescriptorPairCarrierKeyWordRecipes
open RouteDescriptorPairSourceKeyRecipePairs

def terminalRecipePair (recipes : RecipePair) : RecipePair :=
  (CarrierNormalizedSourceKeyRecipes.terminalRecipe recipes.1,
    CarrierNormalizedSourceKeyRecipes.terminalRecipe recipes.2)

def terminalRecipePairBlocks : List (List RecipePair) :=
  RouteDescriptorPairAffine.terminalSourceKeyRecipePairBlocks.map fun block =>
    block.map terminalRecipePair

def crossingRecipePair (shift : Cell) (recipes : RecipePair) : RecipePair :=
  (CarrierNormalizedSourceKeyRecipes.crossingRecipe shift recipes.1,
    CarrierNormalizedSourceKeyRecipes.crossingRecipe shift recipes.2)

def crossingShiftRecipePairBlock
    (occurrences : RouteDescriptorPairAffine.Occurrence ×
      RouteDescriptorPairAffine.Occurrence)
    (shift : Cell) : List RecipePair :=
  (RouteDescriptorPairAffine.occurrencePairCrossingSourceKeyShiftRecipePairBlock
    occurrences shift).map (crossingRecipePair shift)

def crossingRecipePairBlock
    (occurrences : RouteDescriptorPairAffine.Occurrence ×
      RouteDescriptorPairAffine.Occurrence) : List RecipePair :=
  carrierCrossingRetentionShifts.flatMap
    (crossingShiftRecipePairBlock occurrences)

def crossingRecipePairBlocks : List (List RecipePair) :=
  RouteDescriptorOccurrenceSlotCrossing.crossingSlots.map fun slot =>
    crossingRecipePairBlock slot.occurrences

/-- A normalized recipe pair represents the normalized source-key identity
of the same physical carrier-node template. -/
def MatchesNodeAtPeriod
    (tokens : List RouteDescriptorPairFieldTags.Token) (period : Nat)
    (recipes : RecipePair)
    (template : PaddedSupportedCandidateBlocks.Template CarrierNode) : Prop :=
  let keys := CarrierNodeNormalizedSourceKeys.pairAtPeriod
    period template.value
  recipes.1.key tokens = keys.1 ∧
    recipes.2.key tokens = keys.2 ∧
    recipes.1.supported = true ∧ recipes.2.supported = true

/-- Normalize one active padded candidate without changing its support bit. -/
def normalizeCandidateAtPeriod (period : Nat)
    (candidate : Candidate CarrierNode) : Candidate CarrierNode :=
  candidate.mapValue (CarrierNodeNormalizedSourceKeys.nodeAtPeriod period)

end CarrierNormalizedSourceKeyRecipePairs
end LeanTrominoes.PeriodicOrthocrossing
