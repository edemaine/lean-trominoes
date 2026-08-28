/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeSourceKeyCandidateWordData
import LeanTrominoes.PeriodicOrthocrossingCarrierNormalizedSourceKeyRecipePairData

/-! # Word semantics of normalized source-key recipe pairs -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierNormalizedSourceKeyRecipePairs

open PaddedSupportedCandidateBlocks
open RouteDescriptorPairCarrierKeyWordRecipes
open RouteDescriptorPairSourceKeyRecipePairs

theorem wordPair_eq_componentPair_normalizeCandidateAtPeriod_activate
    (tokens : List RouteDescriptorPairFieldTags.Token) (period : Nat)
    (active : Bool) (recipes : RecipePair)
    (template : Template CarrierNode)
    (aligned : MatchesNodeAtPeriod tokens period recipes template) :
    wordPair tokens active recipes =
      CarrierNodeSourceKeyCandidateWords.componentPair
        (normalizeCandidateAtPeriod period (template.activate active)) := by
  rcases aligned with
    ⟨firstValue, secondValue, firstSupported, secondSupported⟩
  cases active <;>
    simp [wordPair, Recipe.word,
      CarrierNodeSourceKeyCandidateWords.componentPair,
      normalizeCandidateAtPeriod,
      PaddedSupportedLastRepresentativeEqualityRows.Candidate.mapValue,
      Template.activate, PaddedSupportedCandidateWords.sentinelWord,
      CarrierNodeNormalizedSourceKeys.pairAtPeriod,
      firstValue, secondValue, firstSupported, secondSupported]

theorem map_wordPair_eq_map_componentPair_normalizeCandidateAtPeriod_activate
    (tokens : List RouteDescriptorPairFieldTags.Token) (period : Nat)
    (active : Bool) (recipes : List RecipePair)
    (templates : List (Template CarrierNode))
    (aligned : List.Forall₂
      (MatchesNodeAtPeriod tokens period) recipes templates) :
    recipes.map (wordPair tokens active) =
      templates.map fun template =>
        CarrierNodeSourceKeyCandidateWords.componentPair
          (normalizeCandidateAtPeriod period
            (template.activate active)) := by
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
              rw [wordPair_eq_componentPair_normalizeCandidateAtPeriod_activate
                  tokens period active recipe template headAligned,
                induction templates tailAligned]

theorem words_eq_map_componentPair_normalizedCandidates
    (tokens : List RouteDescriptorPairFieldTags.Token) (period : Nat)
    (actives : List Bool) (recipeBlocks : List (List RecipePair))
    (templateBlocks : List (List (Template CarrierNode)))
    (aligned : List.Forall₂
      (List.Forall₂ (MatchesNodeAtPeriod tokens period))
      recipeBlocks templateBlocks) :
    RouteDescriptorPairSourceKeyRecipePairs.words
        tokens actives recipeBlocks =
      (candidates actives templateBlocks).map fun candidate =>
        CarrierNodeSourceKeyCandidateWords.componentPair
          (normalizeCandidateAtPeriod period candidate) := by
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
                  rw [RouteDescriptorPairSourceKeyRecipePairs.words,
                    candidates, List.map_append,
                    map_wordPair_eq_map_componentPair_normalizeCandidateAtPeriod_activate
                      tokens period active recipes templates headAligned,
                    induction recipeBlocks templateBlocks tailAligned]
                  simp only [List.map_map, Function.comp_def]

end CarrierNormalizedSourceKeyRecipePairs
end LeanTrominoes.PeriodicOrthocrossing
