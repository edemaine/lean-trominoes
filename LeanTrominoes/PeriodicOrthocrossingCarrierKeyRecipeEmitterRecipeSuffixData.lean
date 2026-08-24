/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterRecipeExecution

/-! # Remaining carrier-key recipe blocks and execution times -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyRecipeEmitterMachine

open RouteDescriptorPairCarrierKeyWordRecipes

def recipeBlocks (recipes : List Recipe)
    (input : List CarrierKeyRecipeEmitter.Token)
    (state : State recipes.length) :
    List (List DelimitedBinaryWords.Token) :=
  List.zipWith (tokenBlock input) state.actives.toList recipes

def recipeTimes (recipes : List Recipe)
    (input : List CarrierKeyRecipeEmitter.Token)
    (state : State recipes.length) : List Nat :=
  List.zipWith (recipeTime input) state.actives.toList recipes

def recipeSuffixTokens (recipes : List Recipe)
    (input : List CarrierKeyRecipeEmitter.Token)
    (state : State recipes.length) (index : Fin recipes.length) :
    List DelimitedBinaryWords.Token :=
  ((recipeBlocks recipes input state).drop index.val).flatten

def recipeSuffixTime (recipes : List Recipe)
    (input : List CarrierKeyRecipeEmitter.Token)
    (state : State recipes.length) (index : Fin recipes.length) : Nat :=
  ((recipeTimes recipes input state).drop index.val).sum

end CarrierKeyRecipeEmitterMachine
end LeanTrominoes.PeriodicOrthocrossing
