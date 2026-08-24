/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateBlocks
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairCarrierKeyWordRecipeData

/-! # Semantics of fixed guarded carrier-key word recipes -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairCarrierKeyWordRecipes

open PaddedSupportedCandidateBlocks
open PaddedSupportedCandidateWords

/-- A recipe represents a template when it recovers the same key and support
bit from the tagged descriptor-pair block. -/
def Recipe.Matches
    (tokens : List RouteDescriptorPairFieldTags.Token)
    (recipe : Recipe) (template : Template CarrierKeyWords.CarrierKey) : Prop :=
  recipe.key tokens = template.value ∧
    recipe.supported = template.supported

/-- One matching recipe emits exactly the guarded word of its activated
candidate template. -/
theorem Recipe.word_eq_guardedWord_activate
    (tokens : List RouteDescriptorPairFieldTags.Token)
    (active : Bool) (recipe : Recipe)
    (template : Template CarrierKeyWords.CarrierKey)
    (aligned : recipe.Matches tokens template) :
    recipe.word tokens active =
      guardedWord CarrierKeyWords.word (template.activate active) := by
  rcases aligned with ⟨valueEq, supportEq⟩
  cases active <;> cases supported : recipe.supported <;>
    simp [Recipe.word, Template.activate, guardedWord,
      sentinelWord, supported, ← supportEq, ← valueEq]

/-- Pointwise matching recipe/template blocks emit the same guarded words. -/
theorem map_word_eq_map_guardedWord_activate
    (tokens : List RouteDescriptorPairFieldTags.Token)
    (active : Bool) (recipes : List Recipe)
    (templates : List (Template CarrierKeyWords.CarrierKey))
    (aligned : List.Forall₂ (Recipe.Matches tokens) recipes templates) :
    recipes.map (Recipe.word tokens active) =
      templates.map (fun template =>
        guardedWord CarrierKeyWords.word (template.activate active)) := by
  induction recipes generalizing templates with
  | nil =>
      cases aligned
      rfl
  | cons recipe recipes induction =>
      cases templates with
      | nil => cases aligned
      | cons template templates =>
          cases aligned with
          | cons headAligned tailAligned =>
              simp only [List.map_cons]
              rw [recipe.word_eq_guardedWord_activate
                tokens active template headAligned,
                induction templates tailAligned]

/-- Aligned matching recipe blocks emit exactly the guarded-word map of the
corresponding padded candidate stream. -/
theorem words_eq_map_guardedWord_candidates
    (tokens : List RouteDescriptorPairFieldTags.Token)
    (actives : List Bool) (recipeBlocks : List (List Recipe))
    (templateBlocks : List
      (List (Template CarrierKeyWords.CarrierKey)))
    (aligned : List.Forall₂
      (List.Forall₂ (Recipe.Matches tokens))
      recipeBlocks templateBlocks) :
    words tokens actives recipeBlocks =
      (candidates actives templateBlocks).map
        (guardedWord CarrierKeyWords.word) := by
  induction actives generalizing recipeBlocks templateBlocks with
  | nil => rfl
  | cons active actives induction =>
      cases recipeBlocks with
      | nil =>
          cases aligned
          rfl
      | cons recipes recipeBlocks =>
          cases templateBlocks with
          | nil => cases aligned
          | cons templates templateBlocks =>
              cases aligned with
              | cons headAligned tailAligned =>
                  rw [words, candidates, List.map_append,
                    map_word_eq_map_guardedWord_activate
                      tokens active recipes templates headAligned,
                    induction recipeBlocks templateBlocks tailAligned]
                  simp only [List.map_map, Function.comp_def]

end RouteDescriptorPairCarrierKeyWordRecipes
end LeanTrominoes.PeriodicOrthocrossing
