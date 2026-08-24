/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterMachineData

/-! # Physical token semantics of compact carrier-key recipes -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyRecipeEmitterMachine

open RouteDescriptorPairCarrierKeyWordRecipes

theorem keyWord_eq_route_prefix
    (input : List CarrierKeyRecipeEmitter.Token) (recipe : Recipe) :
    CarrierKeyWords.word (CarrierKeyRecipeEmitter.preparedKey input recipe) =
      List.replicate
          (CarrierKeyRecipeEmitter.routeCount input recipe.side) false ++
        fixedSuffixBits recipe := by
  unfold CarrierKeyWords.word CarrierKeyRecipeEmitter.preparedKey
    CarrierKeyWords.natField fixedSuffixBits
  rw [show CarrierKeyWords.natField recipe.segmentIndex =
    List.replicate recipe.segmentIndex false ++ [true] by rfl]
  simp [List.append_assoc]

theorem activeTokens_eq_wordTokens
    (input : List CarrierKeyRecipeEmitter.Token) (recipe : Recipe) :
    activeTokens input recipe =
      DelimitedBinaryWords.wordTokens
        (true :: CarrierKeyWords.word
          (CarrierKeyRecipeEmitter.preparedKey input recipe)) := by
  unfold activeTokens activePrefixTokens activeSuffixTokens
    DelimitedBinaryWords.wordTokens
  rw [keyWord_eq_route_prefix]
  simp [List.map_append, List.append_assoc]

@[simp] theorem tokenBlock_eq_wordTokens
    (input : List CarrierKeyRecipeEmitter.Token)
    (active : Bool) (recipe : Recipe) :
    tokenBlock input active recipe =
      DelimitedBinaryWords.wordTokens
        (CarrierKeyRecipeEmitter.preparedWord input active recipe) := by
  unfold tokenBlock CarrierKeyRecipeEmitter.preparedWord
  by_cases enabled : active && recipe.supported
  · rw [if_pos enabled, if_pos enabled, activeTokens_eq_wordTokens]
  · rw [if_neg enabled, if_neg enabled]
    rfl

/-- The physical stream specified by the machine data is exactly the finite
encoding of the semantic compact-emitter output. -/
@[simp] theorem emittedTokens_eq_encode (recipes : List Recipe)
    (input : List CarrierKeyRecipeEmitter.Token) :
    emittedTokens recipes input =
      DelimitedBinaryWords.encode
        (CarrierKeyRecipeEmitter.output recipes input) := by
  unfold emittedTokens DelimitedBinaryWords.encode
    CarrierKeyRecipeEmitter.output CarrierKeyRecipeEmitter.words
  generalize activationEq :
    CarrierKeyRecipeEmitter.activationBits input = actives
  clear activationEq
  induction actives generalizing recipes with
  | nil => rfl
  | cons active actives induction =>
      cases recipes with
      | nil => rfl
      | cons recipe recipes =>
          simp only [List.zipWith_cons_cons, List.flatten_cons,
            List.flatMap_cons]
          rw [tokenBlock_eq_wordTokens, induction]

end CarrierKeyRecipeEmitterMachine
end LeanTrominoes.PeriodicOrthocrossing
