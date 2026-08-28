/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCrossingSourceKeyRecipeEmitterCompiler
import LeanTrominoes.PeriodicOrthocrossingTerminalSourceKeyRecipeEmitterCompiler

/-! # Fixed normalized source-key recipes for carrier candidates -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierNormalizedSourceKeyRecipes

open RouteDescriptorPairCarrierKeyWordRecipes

/-- Zero the known finite translate of one terminal source-key recipe. -/
def terminalRecipe (recipe : Recipe) : Recipe :=
  { recipe with translate := (0, 0) }

/-- Normalized terminal recipes preserve the exact physical recipe order. -/
def terminalRecipes : List Recipe :=
  TerminalSourceKeyRecipeEmitter.recipes.map terminalRecipe

/-- Remove one known common retention shift from a crossing source-key
recipe. -/
def crossingRecipe (shift : Cell) (recipe : Recipe) : Recipe :=
  { recipe with translate := Cell.sub recipe.translate shift }

/-- One normalized doubled source-key block for a fixed occurrence pair and
one physical retention shift. -/
def crossingShiftRecipeBlock
    (occurrences : RouteDescriptorPairAffine.Occurrence ×
      RouteDescriptorPairAffine.Occurrence)
    (shift : Cell) : List Recipe :=
  (RouteDescriptorPairAffine.occurrencePairCrossingSourceKeyShiftRecipeBlock
    occurrences shift).map (crossingRecipe shift)

/-- Repeat the same normalized boundary source identities at every physical
retention-shift slot. -/
def crossingRecipeBlock
    (occurrences : RouteDescriptorPairAffine.Occurrence ×
      RouteDescriptorPairAffine.Occurrence) : List Recipe :=
  carrierCrossingRetentionShifts.flatMap
    (crossingShiftRecipeBlock occurrences)

def crossingRecipeBlocks : List (List Recipe) :=
  RouteDescriptorOccurrenceSlotCrossing.crossingSlots.map fun slot =>
    crossingRecipeBlock slot.occurrences

def crossingRecipes : List Recipe :=
  crossingRecipeBlocks.flatten

/-- Semantic normalized terminal word package produced from the existing
physical activation preparation. -/
def terminalOutput (tokens : List RouteDescriptorPairFieldTags.Token) :
    DelimitedBinaryWords.Input :=
  CarrierKeyRecipeEmitter.output terminalRecipes
    (TerminalSourceKeyRecipeEmitter.preparedInput tokens)

/-- Semantic normalized crossing word package produced from the existing
physical activation preparation. -/
def crossingOutput
    (tokens : List RouteDescriptorOccurrenceSlotPairFieldTags.Token) :
    DelimitedBinaryWords.Input :=
  CarrierKeyRecipeEmitter.output crossingRecipes
    (CrossingSourceKeyRecipeEmitter.preparedInput tokens)

@[simp] theorem terminalRecipes_length :
    terminalRecipes.length = TerminalSourceKeyRecipeEmitter.recipes.length := by
  simp [terminalRecipes]

@[simp] theorem crossingShiftRecipeBlock_length
    (occurrences : RouteDescriptorPairAffine.Occurrence ×
      RouteDescriptorPairAffine.Occurrence)
    (shift : Cell) :
    (crossingShiftRecipeBlock occurrences shift).length =
      (RouteDescriptorPairAffine.occurrencePairCrossingSourceKeyShiftRecipeBlock
        occurrences shift).length := by
  simp [crossingShiftRecipeBlock]

theorem crossingRecipeBlock_length
    (occurrences : RouteDescriptorPairAffine.Occurrence ×
      RouteDescriptorPairAffine.Occurrence) :
    (crossingRecipeBlock occurrences).length =
      (RouteDescriptorPairAffine.occurrencePairCrossingSourceKeyRecipeBlock
        occurrences).length := by
  unfold crossingRecipeBlock
    RouteDescriptorPairAffine.occurrencePairCrossingSourceKeyRecipeBlock
  induction carrierCrossingRetentionShifts with
  | nil => rfl
  | cons shift shifts induction =>
      simp only [List.flatMap_cons, List.length_append]
      rw [crossingShiftRecipeBlock_length, induction]

@[simp] theorem crossingRecipes_length :
    crossingRecipes.length = CrossingSourceKeyRecipeEmitter.recipes.length := by
  unfold crossingRecipes crossingRecipeBlocks
    CrossingSourceKeyRecipeEmitter.recipes
    RouteDescriptorOccurrenceSlotCrossing.crossingSourceKeyRecipeBlocks
    RouteDescriptorOccurrenceSlotCrossing.Slot.sourceKeyRecipeBlock
  induction RouteDescriptorOccurrenceSlotCrossing.crossingSlots with
  | nil => rfl
  | cons slot slots induction =>
      simp only [List.map_cons, List.flatten_cons, List.length_append]
      rw [crossingRecipeBlock_length, induction]

end CarrierNormalizedSourceKeyRecipes
end LeanTrominoes.PeriodicOrthocrossing
