/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNormalizedSourceKeyRecipePairData
import LeanTrominoes.PeriodicOrthocrossingCrossingSourceKeyRecipePairComponentSemantics
import LeanTrominoes.PeriodicOrthocrossingTerminalSourceKeyRecipePairComponentSemantics

/-! # Component layouts of normalized source-key recipe pairs -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierNormalizedSourceKeyRecipePairs

open RouteDescriptorPairCarrierKeyWordRecipes
open RouteDescriptorPairSourceKeyRecipePairs

private theorem flatten_map_map
    {Source Target : Type*} (project : Source → Target)
    (blocks : List (List Source)) :
    (blocks.map fun block => block.map project).flatten =
      blocks.flatten.map project := by
  induction blocks with
  | nil => rfl
  | cons block blocks induction =>
      simp only [List.map_cons, List.flatten_cons, List.map_append,
        induction]

private theorem componentRecipeBlock_map_terminalRecipePair
    (block : List RecipePair) :
    componentRecipeBlock (block.map terminalRecipePair) =
      (componentRecipeBlock block).map
        CarrierNormalizedSourceKeyRecipes.terminalRecipe := by
  unfold componentRecipeBlock
  rw [List.flatMap_map, List.map_flatMap]
  apply List.flatMap_congr
  intro recipes _recipesMember
  rfl

private theorem componentRecipeBlock_map_crossingRecipePair
    (shift : Cell) (block : List RecipePair) :
    componentRecipeBlock (block.map (crossingRecipePair shift)) =
      (componentRecipeBlock block).map
        (CarrierNormalizedSourceKeyRecipes.crossingRecipe shift) := by
  unfold componentRecipeBlock
  rw [List.flatMap_map, List.map_flatMap]
  apply List.flatMap_congr
  intro recipes _recipesMember
  rfl

private theorem componentRecipeBlocks_map_terminalRecipePair
    (blocks : List (List RecipePair)) :
    componentRecipeBlocks
        (blocks.map fun block => block.map terminalRecipePair) =
      (componentRecipeBlocks blocks).map fun block =>
        block.map CarrierNormalizedSourceKeyRecipes.terminalRecipe := by
  unfold componentRecipeBlocks
  rw [List.map_map, List.map_map]
  apply List.map_congr_left
  intro block _blockMember
  exact componentRecipeBlock_map_terminalRecipePair block

@[simp] theorem terminalComponentRecipeBlocks :
    componentRecipeBlocks terminalRecipePairBlocks =
      RouteDescriptorPairAffine.terminalSourceKeyRecipeBlocks.map fun block =>
        block.map CarrierNormalizedSourceKeyRecipes.terminalRecipe := by
  unfold terminalRecipePairBlocks
  rw [componentRecipeBlocks_map_terminalRecipePair,
    RouteDescriptorPairAffine.componentRecipeBlocks_terminalSourceKeyRecipePairBlocks]

@[simp] theorem terminalComponentRecipes :
    (componentRecipeBlocks terminalRecipePairBlocks).flatten =
      CarrierNormalizedSourceKeyRecipes.terminalRecipes := by
  unfold CarrierNormalizedSourceKeyRecipes.terminalRecipes
    TerminalSourceKeyRecipeEmitter.recipes
  rw [terminalComponentRecipeBlocks, flatten_map_map]

private theorem expandedActives_map_blocks
    (actives : List Bool) (blocks : List (List Recipe))
    (project : Recipe → Recipe) :
    expandedActives actives
        (blocks.map fun block => block.map project) =
      expandedActives actives blocks := by
  induction actives generalizing blocks with
  | nil => cases blocks <;> rfl
  | cons active actives induction =>
      cases blocks with
      | nil => rfl
      | cons block blocks =>
          simp only [List.map_cons, expandedActives, List.length_map]
          rw [induction blocks]

theorem terminalExpandedActives
    (actives : List Bool) :
    expandedActives actives
        (componentRecipeBlocks terminalRecipePairBlocks) =
      expandedActives actives
        RouteDescriptorPairAffine.terminalSourceKeyRecipeBlocks := by
  rw [terminalComponentRecipeBlocks]
  exact expandedActives_map_blocks actives
    RouteDescriptorPairAffine.terminalSourceKeyRecipeBlocks
    CarrierNormalizedSourceKeyRecipes.terminalRecipe

@[simp] theorem crossingShiftComponentRecipes
    (occurrences : RouteDescriptorPairAffine.Occurrence ×
      RouteDescriptorPairAffine.Occurrence)
    (shift : Cell) :
    componentRecipeBlock
        (crossingShiftRecipePairBlock occurrences shift) =
      CarrierNormalizedSourceKeyRecipes.crossingShiftRecipeBlock
        occurrences shift := by
  unfold crossingShiftRecipePairBlock
    CarrierNormalizedSourceKeyRecipes.crossingShiftRecipeBlock
  rw [componentRecipeBlock_map_crossingRecipePair,
    RouteDescriptorPairAffine.componentRecipeBlock_occurrencePairCrossingSourceKeyShiftRecipePairBlock]

@[simp] theorem crossingComponentRecipeBlock
    (occurrences : RouteDescriptorPairAffine.Occurrence ×
      RouteDescriptorPairAffine.Occurrence) :
    componentRecipeBlock (crossingRecipePairBlock occurrences) =
      CarrierNormalizedSourceKeyRecipes.crossingRecipeBlock occurrences := by
  unfold crossingRecipePairBlock
    CarrierNormalizedSourceKeyRecipes.crossingRecipeBlock
    componentRecipeBlock
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro shift _shiftMember
  exact crossingShiftComponentRecipes occurrences shift

@[simp] theorem crossingComponentRecipeBlocks :
    componentRecipeBlocks crossingRecipePairBlocks =
      CarrierNormalizedSourceKeyRecipes.crossingRecipeBlocks := by
  unfold crossingRecipePairBlocks
    CarrierNormalizedSourceKeyRecipes.crossingRecipeBlocks
    componentRecipeBlocks
  rw [List.map_map]
  apply List.map_congr_left
  intro slot _slotMember
  exact crossingComponentRecipeBlock slot.occurrences

theorem crossingExpandedActives
    (actives : List Bool) :
    expandedActives actives
        (componentRecipeBlocks crossingRecipePairBlocks) =
      expandedActives actives
        RouteDescriptorOccurrenceSlotCrossing.crossingSourceKeyRecipeBlocks := by
  rw [crossingComponentRecipeBlocks]
  unfold CarrierNormalizedSourceKeyRecipes.crossingRecipeBlocks
    RouteDescriptorOccurrenceSlotCrossing.crossingSourceKeyRecipeBlocks
    RouteDescriptorOccurrenceSlotCrossing.Slot.sourceKeyRecipeBlock
  have aligned : ∀ (left : List Bool)
      (slots : List RouteDescriptorOccurrenceSlotCrossing.Slot),
      expandedActives left
          (slots.map fun slot =>
            CarrierNormalizedSourceKeyRecipes.crossingRecipeBlock
              slot.occurrences) =
        expandedActives left
          (slots.map fun slot =>
            RouteDescriptorPairAffine.occurrencePairCrossingSourceKeyRecipeBlock
              slot.occurrences) := by
    intro left
    induction left with
    | nil => intro slots; cases slots <;> rfl
    | cons active left induction =>
        intro slots
        cases slots with
        | nil => rfl
        | cons slot slots =>
            simp only [List.map_cons, expandedActives]
            rw [CarrierNormalizedSourceKeyRecipes.crossingRecipeBlock_length,
              induction slots]
  exact aligned actives RouteDescriptorOccurrenceSlotCrossing.crossingSlots

@[simp] theorem crossingComponentRecipes :
    (componentRecipeBlocks crossingRecipePairBlocks).flatten =
      CarrierNormalizedSourceKeyRecipes.crossingRecipes := by
  rw [crossingComponentRecipeBlocks]
  rfl

end CarrierNormalizedSourceKeyRecipePairs
end LeanTrominoes.PeriodicOrthocrossing
