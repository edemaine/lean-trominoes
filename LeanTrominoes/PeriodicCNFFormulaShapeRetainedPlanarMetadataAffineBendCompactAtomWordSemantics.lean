/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendCompactAtomWordData
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendPredicateSemantics
import LeanTrominoes.PeriodicOrthocrossingGuardedCarrierKeyCompactAtomWordSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteBendCompactAtomWordData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairFieldValueSemantics

/-! # Local semantics of affine compact retained-bend atom words -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open PlanarThreeSAT RouteDescriptorPairFieldTags
open GuardedCarrierKeyCompactAtomWords

/-- Rejection-sentinel removal from the guarded affine recipe family. -/
def bendCompactAtomWords
    (tokens : List RouteDescriptorPairFieldTags.Token) : List (List Bool) :=
  GuardedCarrierKeyCompactAtomWords.words
    (bendCompactAtomGuardedWords tokens)

/-- Sentinel removal is exactly ordinary predicate-selected block output. -/
theorem bendCompactAtomWords_eq_predicateListBlocks
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    bendCompactAtomWords tokens =
      predicateListBlocks bendDescriptorPredicates
        (bendCompactAtomWordRecipeBlocks.map
          (recipeBlockWords tokens)) tokens := by
  unfold bendCompactAtomWords bendCompactAtomGuardedWords
  rw [words_recipe_words, predicateListBlocks_eq]

/-- Interpreting the four fixed recipes at one descriptor pair gives exactly
the four compact occurrence words of the evaluated bend template. -/
@[simp] theorem BendTemplate.recipeBlockWords_compactAtomWordRecipes
    (template : BendTemplate)
    (pair : RouteDescriptor × RouteDescriptor) :
    recipeBlockWords (descriptorPairTokens pair)
        template.compactAtomWordRecipes =
      (template.evalPair .first pair).compactAtomWords := by
  rcases pair with ⟨first, second⟩
  simp [recipeBlockWords, recipeWords,
    BendTemplate.compactAtomWordRecipes,
    BendTemplate.compactTerminalRecipe,
    RouteBend.compactAtomWords,
    SegmentTerminal.compactAtomWord,
    RouteBend.incomingTerminal,
    RouteBend.outgoingTerminal,
    SegmentTerminal.carrierKey,
    CarrierNodeSourceKeys.taggedKey,
    RouteDescriptorPairCarrierKeyWordRecipes.Recipe.key,
    tokenFieldValue_descriptorPairTokens,
    BendTemplate.evalPair, descriptorAt,
    PeriodicGridDrawing.SegmentOccurrenceKey,
    pairFieldValue, descriptorFieldValue,
    RouteDescriptor.unaryFields, signedUnaryFields]

/-- The sixteen compass-port predicates retain exactly one copy of the
evaluated bend's four compact occurrence words. -/
theorem BendTemplate.descriptorPredicates_selectedCompactAtomWords
    (shape : RouteShape) (template : BendTemplate)
    (pair : RouteDescriptor × RouteDescriptor)
    (sameEdge : pair.1.edgeIndex = pair.2.edgeIndex)
    (shapeMatches : shape.Matches pair.1)
    (incomingGenuine :
      (AxisDirection.between
        (template.incomingStart.evalPair pair)
        (template.bend.evalPair pair)).IsGenuine)
    (outgoingGenuine :
      (AxisDirection.between
        (template.bend.evalPair pair)
        (template.outgoingFinish.evalPair pair)).IsGenuine) :
    predicateListBlocks
        (template.descriptorPredicates shape)
        ((template.compactAtomWordRecipeBlocks shape).map
          (recipeBlockWords (descriptorPairTokens pair)))
        (descriptorPairTokens pair) =
      (template.evalPair .first pair).compactAtomWords := by
  rw [predicateListBlocks_eq]
  unfold BendTemplate.descriptorPredicates
    BendTemplate.compactAtomWordRecipeBlocks
  rw [List.map_map, List.map_map]
  simp only [Predicate.evalTokens_descriptorPairTokens]
  change
    selectTruthBlocks
        (allCornerPortPairs.map fun _ =>
          recipeBlockWords (descriptorPairTokens pair)
            template.compactAtomWordRecipes)
        (allCornerPortPairs.map fun ports =>
          (template.descriptorPredicate shape ports).evalPair pair) = _
  simp_rw [BendTemplate.descriptorPredicate_evalPair shape template _ pair
    sameEdge shapeMatches incomingGenuine outgoingGenuine]
  generalize incomingEq :
      (template.evalPair .first pair).incomingPort = incoming
  generalize outgoingEq :
      (template.evalPair .first pair).outgoingPort = outgoing
  cases incoming <;> cases outgoing <;>
    simp [allCornerPortPairs, allCornerPorts, selectTruthBlocks]

end RouteDescriptorPairAffine
end PeriodicOrthocrossing
end LeanTrominoes
