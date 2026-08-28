/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRoutedVariableCompactAtomWordEmitterCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairCarrierKeyWordRecipeActivationLength
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairCarrierKeyWordRecipeActivationSemantics

/-! # Semantics of guarded routed-variable compact-word emission -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RoutedVariableCompactAtomWordEmitter

open RouteDescriptorPairCarrierKeyWordRecipes

private theorem activationBits_indexTokens
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    CarrierKeyRecipeEmitter.activationBits (indexTokens tokens) = [] := by
  induction tokens with
  | nil => rfl
  | cons token tokens induction =>
      unfold indexTokens at induction ⊢
      unfold CarrierKeyRecipeEmitter.activationBits at induction ⊢
      rw [List.flatMap_cons, List.filterMap_append]
      cases token with
      | pairStart => simpa [indexBlock] using induction
      | pairEnd => simpa [indexBlock] using induction
      | unit side field =>
          cases side
          · by_cases fieldEq : field = 4 <;>
              simp [indexBlock, fieldEq, induction]
          · by_cases fieldEq : field = 2 <;>
              simp [indexBlock, fieldEq, induction]

@[simp] theorem preparedInput_activationBits
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    CarrierKeyRecipeEmitter.activationBits (preparedInput tokens) =
      RouteDescriptorPairAffine.routedVariableCompactAtomWordExpandedActives
        tokens := by
  unfold preparedInput activationTokens
  rw [CarrierKeyRecipeEmitter.activationBits]
  rw [List.filterMap_append]
  change CarrierKeyRecipeEmitter.activationBits (indexTokens tokens) ++ _ = _
  rw [activationBits_indexTokens]
  simp [CarrierKeyRecipeEmitter.activationTokens]

private theorem indexTokens_count_first
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    (indexTokens tokens).count (.routeUnit .first) =
      tokens.count (.unit .first 4) := by
  induction tokens with
  | nil => rfl
  | cons token tokens induction =>
      unfold indexTokens at induction ⊢
      rw [List.flatMap_cons, List.count_append]
      cases token with
      | pairStart => simpa [indexBlock] using induction
      | pairEnd => simpa [indexBlock] using induction
      | unit side field =>
          cases side
          · by_cases fieldEq : field = 4
            · subst field
              simp [indexBlock, induction, Nat.add_comm]
            · simpa [indexBlock, fieldEq] using induction
          · by_cases fieldEq : field = 2
            · subst field
              simp [indexBlock, induction]
            · simpa [indexBlock, fieldEq] using induction

private theorem indexTokens_count_second
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    (indexTokens tokens).count (.routeUnit .second) =
      tokens.count (.unit .second 2) := by
  induction tokens with
  | nil => rfl
  | cons token tokens induction =>
      unfold indexTokens at induction ⊢
      rw [List.flatMap_cons, List.count_append]
      cases token with
      | pairStart => simpa [indexBlock] using induction
      | pairEnd => simpa [indexBlock] using induction
      | unit side field =>
          cases side
          · by_cases fieldEq : field = 4
            · subst field
              simp [indexBlock, induction]
            · simpa [indexBlock, fieldEq] using induction
          · by_cases fieldEq : field = 2
            · subst field
              simp [indexBlock, induction, Nat.add_comm]
            · simpa [indexBlock, fieldEq] using induction

private theorem activationTokens_routeCount_zero
    (tokens : List RouteDescriptorPairFieldTags.Token)
    (side : RouteDescriptorPairFieldTags.Side) :
    (activationTokens tokens).count (.routeUnit side) = 0 := by
  unfold activationTokens CarrierKeyRecipeEmitter.activationTokens
  exact CarrierKeyRecipeEmitter.activation_route_count_zero _ side

@[simp] theorem preparedInput_routeCount_first
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    CarrierKeyRecipeEmitter.routeCount (preparedInput tokens) .first =
      RouteDescriptorPairFieldTags.tokenFieldValue tokens .first 4 := by
  unfold CarrierKeyRecipeEmitter.routeCount preparedInput
    RouteDescriptorPairFieldTags.tokenFieldValue
  rw [List.count_append, indexTokens_count_first,
    activationTokens_routeCount_zero, Nat.add_zero]

@[simp] theorem preparedInput_routeCount_second
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    CarrierKeyRecipeEmitter.routeCount (preparedInput tokens) .second =
      RouteDescriptorPairFieldTags.tokenFieldValue tokens .second 2 := by
  unfold CarrierKeyRecipeEmitter.routeCount preparedInput
    RouteDescriptorPairFieldTags.tokenFieldValue
  rw [List.count_append, indexTokens_count_second,
    activationTokens_routeCount_zero, Nat.add_zero]

@[simp] theorem preparedWord_eq
    (tokens : List RouteDescriptorPairFieldTags.Token)
    (active : Bool) (recipe : Recipe) :
    CarrierKeyRecipeEmitter.preparedWord (preparedInput tokens)
        active recipe =
      RouteDescriptorPairAffine.routedVariableCompactAtomRecipeWord
        tokens active recipe := by
  unfold CarrierKeyRecipeEmitter.preparedWord
    CarrierKeyRecipeEmitter.preparedKey
    RouteDescriptorPairAffine.routedVariableCompactAtomRecipeWord
    RouteDescriptorPairAffine.routedVariableCompactAtomRecipeKey
  cases recipe.side <;> simp

private theorem recipeWords_eq_zip
    (tokens : List RouteDescriptorPairFieldTags.Token)
    (actives : List Bool) (blocks : List (List Recipe)) :
    RouteDescriptorPairAffine.routedVariableCompactAtomRecipeWords
        tokens actives blocks =
      List.zipWith
        (RouteDescriptorPairAffine.routedVariableCompactAtomRecipeWord
          tokens)
        (expandedActives actives blocks) blocks.flatten := by
  induction actives generalizing blocks with
  | nil => simp [RouteDescriptorPairAffine.routedVariableCompactAtomRecipeWords,
      expandedActives]
  | cons active actives induction =>
      cases blocks with
      | nil => rfl
      | cons block blocks =>
          rw [RouteDescriptorPairAffine.routedVariableCompactAtomRecipeWords,
            expandedActives, List.flatten_cons]
          rw [zipWith_replicate_length_append]
          rw [induction]

private theorem preparedWords_eq_zip
    (tokens : List RouteDescriptorPairFieldTags.Token)
    (actives : List Bool) (recipeList : List Recipe) :
    List.zipWith
        (CarrierKeyRecipeEmitter.preparedWord (preparedInput tokens))
        actives recipeList =
      List.zipWith
        (RouteDescriptorPairAffine.routedVariableCompactAtomRecipeWord
          tokens)
        actives recipeList := by
  induction actives generalizing recipeList with
  | nil => rfl
  | cons active actives induction =>
      cases recipeList with
      | nil => rfl
      | cons recipe recipes =>
          simp only [List.zipWith_cons_cons]
          rw [preparedWord_eq, induction]

@[simp] theorem expandedActives_length
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    (RouteDescriptorPairAffine.routedVariableCompactAtomWordExpandedActives
      tokens).length = recipes.length := by
  rw [RouteDescriptorPairAffine.routedVariableCompactAtomWordExpandedActives_eq]
  unfold recipes
  apply expandedActives_length_of_length_eq
  rw [List.length_map]
  exact
    RouteDescriptorPairAffine.routedVariableCompactAtomWordRecipeBlocks_length.symm

@[simp] theorem preparedInput_activationBits_length
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    (CarrierKeyRecipeEmitter.activationBits
      (preparedInput tokens)).length = recipes.length := by
  rw [preparedInput_activationBits]
  exact expandedActives_length tokens

theorem output_eq
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    CarrierKeyRecipeEmitter.output recipes (preparedInput tokens) =
      ⟨RouteDescriptorPairAffine.routedVariableCompactAtomGuardedWords
        tokens⟩ := by
  unfold CarrierKeyRecipeEmitter.output CarrierKeyRecipeEmitter.words
  rw [preparedInput_activationBits]
  rw [preparedWords_eq_zip]
  rw [RouteDescriptorPairAffine.routedVariableCompactAtomWordExpandedActives_eq]
  unfold recipes
  rw [← recipeWords_eq_zip]
  rfl

/-- Physical emission is exactly the delimiter encoding of the guarded
routed-variable recipe words. -/
@[simp] theorem emittedTokens_eq_encode
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    emittedTokens tokens =
      DelimitedBinaryWords.encode
        ⟨RouteDescriptorPairAffine.routedVariableCompactAtomGuardedWords
          tokens⟩ := by
  unfold emittedTokens
  rw [CarrierKeyRecipeEmitterMachine.compiledTokens_eq_emittedTokens
      recipes (preparedInput tokens)
      (preparedInput_activationBits_length tokens),
    CarrierKeyRecipeEmitterMachine.emittedTokens_eq_encode,
    output_eq]

end RoutedVariableCompactAtomWordEmitter
end LeanTrominoes.PeriodicOrthocrossing
