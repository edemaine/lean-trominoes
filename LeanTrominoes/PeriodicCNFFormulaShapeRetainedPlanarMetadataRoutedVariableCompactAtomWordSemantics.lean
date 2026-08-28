/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableCompactAtomWordData
import LeanTrominoes.PeriodicOrthocrossingRoutedVariableCompactAtomWordCleanupSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairFieldValueSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairRouteShapeSegmentSemantics

/-! # Local semantics of routed-variable compact atom words -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags
open RouteDescriptorPairCarrierKeyWordRecipes

/-- Remove inactive sentinels and interpret the alternating terminal/source-
atom recipe positions. -/
def routedVariableCompactAtomWords
    (tokens : List RouteDescriptorPairFieldTags.Token) : List (List Bool) :=
  RoutedVariableCompactAtomWordCleanup.words
    (routedVariableCompactAtomGuardedWords tokens)

theorem firstNatField_natField_append
    (number : Nat) (suffix : List Bool) :
    RoutedVariableCompactAtomWordCleanup.firstNatField
        (CarrierKeyWords.natField number ++ suffix) =
      CarrierKeyWords.natField number := by
  unfold CarrierKeyWords.natField
  induction number with
  | zero => rfl
  | succ number induction =>
      simp only [List.replicate_succ, List.cons_append,
        RoutedVariableCompactAtomWordCleanup.firstNatField,
        List.cons.injEq, true_and]
      exact induction

@[simp] theorem cleanup_sourceAtomRecipe
    (pair : RouteDescriptor × RouteDescriptor) :
    RoutedVariableCompactAtomWordCleanup.word .sourceAtom
        (routedVariableCompactAtomRecipeWord
          (descriptorPairTokens pair) true
          routedVariableSourceAtomRecipe) =
      [RouteDescriptorTargetAtomWords.word pair.1] := by
  simp [routedVariableCompactAtomRecipeWord,
    routedVariableCompactAtomRecipeKey,
    routedVariableSourceAtomRecipe,
    RouteDescriptorTargetAtomWords.word,
    CarrierKeyWords.word,
    RoutedVariableCompactAtomWordCleanup.word,
    firstNatField_natField_append,
    tokenFieldValue_descriptorPairTokens,
    pairFieldValue, descriptorFieldValue,
    RouteDescriptor.unaryFields, signedUnaryFields]

@[simp] theorem RouteShape.cleanup_targetTerminalRecipe
    (shape : RouteShape)
    (pair : RouteDescriptor × RouteDescriptor)
    (shapeMatches : shape.Matches pair.2) :
    RoutedVariableCompactAtomWordCleanup.word .terminal
        (routedVariableCompactAtomRecipeWord
          (descriptorPairTokens pair) true
          shape.routedVariableTargetTerminalRecipe) =
      [routeDescriptorTargetTerminalCompactAtomWord pair.2] := by
  have segmentsEq := shape.map_evalPair_segments
    .second pair shapeMatches
  have lengthEq := congrArg List.length segmentsEq
  simp only [List.length_map] at lengthEq
  simp [routedVariableCompactAtomRecipeWord,
    routedVariableCompactAtomRecipeKey,
    RouteShape.routedVariableTargetTerminalRecipe,
    routeDescriptorTargetTerminalCompactAtomWord,
    RoutedVariableCompactAtomWordCleanup.word,
    tokenFieldValue_descriptorPairTokens,
    pairFieldValue, descriptorFieldValue,
    RouteDescriptor.unaryFields, signedUnaryFields,
    descriptorAt, lengthEq]

/-- An active route-shape block cleans to the exact four compact atom words
of its selected routed-variable equality. -/
theorem RouteShape.cleanup_activeRecipeBlock
    (shape : RouteShape)
    (pair : RouteDescriptor × RouteDescriptor)
    (shapeMatches : shape.Matches pair.2) :
    RoutedVariableCompactAtomWordCleanup.words
        (shape.routedVariableCompactAtomWordRecipes.map
          (routedVariableCompactAtomRecipeWord
            (descriptorPairTokens pair) true)) =
      routedVariableCompactAtomWordBlock pair.1 pair.2 := by
  unfold RouteShape.routedVariableCompactAtomWordRecipes
    routedVariableCompactAtomWordBlock
    RoutedVariableCompactAtomWordCleanup.words
  simp only [List.map_cons, List.map_nil]
  change
    RoutedVariableCompactAtomWordCleanup.word .terminal
          (routedVariableCompactAtomRecipeWord
            (descriptorPairTokens pair) true
            shape.routedVariableTargetTerminalRecipe) ++
        RoutedVariableCompactAtomWordCleanup.word .sourceAtom
          (routedVariableCompactAtomRecipeWord
            (descriptorPairTokens pair) true
            routedVariableSourceAtomRecipe) ++
        RoutedVariableCompactAtomWordCleanup.word .terminal
          (routedVariableCompactAtomRecipeWord
            (descriptorPairTokens pair) true
            shape.routedVariableTargetTerminalRecipe) ++
        RoutedVariableCompactAtomWordCleanup.word .sourceAtom
          (routedVariableCompactAtomRecipeWord
            (descriptorPairTokens pair) true
            routedVariableSourceAtomRecipe) = _
  rw [shape.cleanup_targetTerminalRecipe pair shapeMatches,
    cleanup_sourceAtomRecipe]
  simp

/-- Four inactive recipes are all discarded and leave the alternating phase
at the beginning of the next block. -/
theorem RouteShape.cleanup_inactiveRecipeBlock
    (shape : RouteShape)
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    RoutedVariableCompactAtomWordCleanup.words
        (shape.routedVariableCompactAtomWordRecipes.map
          (routedVariableCompactAtomRecipeWord tokens false)) = [] := by
  simp [RouteShape.routedVariableCompactAtomWordRecipes,
    routedVariableCompactAtomRecipeWord,
    RoutedVariableCompactAtomWordCleanup.words,
    RoutedVariableCompactAtomWordCleanup.wordsFrom,
    RoutedVariableCompactAtomWordCleanup.word,
    RoutedVariableCompactAtomWordCleanup.Kind.next,
    PaddedSupportedCandidateWords.sentinelWord]

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
