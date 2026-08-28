/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendBaseSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableCompactAtomWordSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariablePairFieldSemantics

/-! # Affine selection of routed-variable compact atom words -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags
open RouteDescriptorPairCarrierKeyWordRecipes
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

def routedVariableCompactAtomWordOutputBlocks
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    List (List (List Bool)) :=
  routedVariableCompactAtomWordRecipeBlocks.map fun block =>
    RoutedVariableCompactAtomWordCleanup.words
      (block.map (routedVariableCompactAtomRecipeWord tokens true))

private theorem cleanup_four_append
    (first second third fourth : List Bool)
    (rest : List (List Bool)) :
    RoutedVariableCompactAtomWordCleanup.words
        ([first, second, third, fourth] ++ rest) =
      RoutedVariableCompactAtomWordCleanup.words
          [first, second, third, fourth] ++
        RoutedVariableCompactAtomWordCleanup.words rest := by
  simp [RoutedVariableCompactAtomWordCleanup.words,
    RoutedVariableCompactAtomWordCleanup.wordsFrom,
    RoutedVariableCompactAtomWordCleanup.Kind.next,
    List.append_assoc]

private theorem cleanup_four_inactive
    (tokens : List RouteDescriptorPairFieldTags.Token)
    (first second third fourth : Recipe) :
    RoutedVariableCompactAtomWordCleanup.words
        ([first, second, third, fourth].map
          (routedVariableCompactAtomRecipeWord tokens false)) = [] := by
  simp [routedVariableCompactAtomRecipeWord,
    RoutedVariableCompactAtomWordCleanup.words,
    RoutedVariableCompactAtomWordCleanup.wordsFrom,
    RoutedVariableCompactAtomWordCleanup.word,
    RoutedVariableCompactAtomWordCleanup.Kind.next,
    PaddedSupportedCandidateWords.sentinelWord]

private theorem cleanup_recipeWords_eq_selectTruthBlocks
    (tokens : List RouteDescriptorPairFieldTags.Token)
    (actives : List Bool) (blocks : List (List Recipe))
    (blocksFour : ∀ block ∈ blocks,
      ∃ first second third fourth,
        block = [first, second, third, fourth]) :
    RoutedVariableCompactAtomWordCleanup.words
        (routedVariableCompactAtomRecipeWords tokens actives blocks) =
      selectTruthBlocks
        (blocks.map fun block =>
          RoutedVariableCompactAtomWordCleanup.words
            (block.map
              (routedVariableCompactAtomRecipeWord tokens true)))
        actives := by
  induction actives generalizing blocks with
  | nil => simp [routedVariableCompactAtomRecipeWords,
      RoutedVariableCompactAtomWordCleanup.words,
      RoutedVariableCompactAtomWordCleanup.wordsFrom,
      selectTruthBlocks]
  | cons active actives induction =>
      cases blocks with
      | nil => rfl
      | cons block blocks =>
          rcases blocksFour block (by simp) with
            ⟨first, second, third, fourth, rfl⟩
          have tailFour : ∀ tail ∈ blocks,
              ∃ first second third fourth,
                tail = [first, second, third, fourth] := by
            intro tail tailMember
            exact blocksFour tail (by simp [tailMember])
          rw [routedVariableCompactAtomRecipeWords]
          rw [show
              [first, second, third, fourth].map
                    (routedVariableCompactAtomRecipeWord tokens active) ++
                  routedVariableCompactAtomRecipeWords tokens actives blocks =
                [routedVariableCompactAtomRecipeWord tokens active first,
                  routedVariableCompactAtomRecipeWord tokens active second,
                  routedVariableCompactAtomRecipeWord tokens active third,
                  routedVariableCompactAtomRecipeWord tokens active fourth] ++
                  routedVariableCompactAtomRecipeWords tokens actives blocks
            by rfl]
          rw [cleanup_four_append]
          rw [induction blocks tailFour]
          cases active
          · simp only [List.map_cons, selectTruthBlocks, if_false,
              List.nil_append]
            have inactive := cleanup_four_inactive tokens
              first second third fourth
            rw [show
              RoutedVariableCompactAtomWordCleanup.words
                  [routedVariableCompactAtomRecipeWord tokens false first,
                    routedVariableCompactAtomRecipeWord tokens false second,
                    routedVariableCompactAtomRecipeWord tokens false third,
                    routedVariableCompactAtomRecipeWord tokens false fourth] =
                [] by simpa using inactive]
            rfl
          · simp only [List.map_cons, selectTruthBlocks, if_true]
            rfl

private theorem routedVariableCompactAtomWordRecipeBlocks_four :
    ∀ block ∈ routedVariableCompactAtomWordRecipeBlocks,
      ∃ first second third fourth,
        block = [first, second, third, fourth] := by
  intro block blockMember
  unfold routedVariableCompactAtomWordRecipeBlocks at blockMember
  rcases List.mem_flatMap.mp blockMember with
    ⟨shape, _shapeMember, blockMember⟩
  unfold RouteShape.routedVariableCompactAtomWordRecipeBlocks at blockMember
  rcases List.mem_map.mp blockMember with
    ⟨rank, _rankMember, rfl⟩
  exact
    ⟨shape.routedVariableTargetTerminalRecipe,
      routedVariableSourceAtomRecipe,
      shape.routedVariableTargetTerminalRecipe,
      routedVariableSourceAtomRecipe, rfl⟩

/-- Alternating cleanup is ordinary affine predicate block selection over
the exact cleaned four-word recipe blocks. -/
theorem routedVariableCompactAtomWords_eq_predicateListBlocks
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    routedVariableCompactAtomWords tokens =
      predicateListBlocks routedVariableCompactAtomWordPredicates
        (routedVariableCompactAtomWordOutputBlocks tokens) tokens := by
  unfold routedVariableCompactAtomWords
    routedVariableCompactAtomGuardedWords
    routedVariableCompactAtomWordOutputBlocks
  rw [predicateListBlocks_eq]
  exact cleanup_recipeWords_eq_selectTruthBlocks tokens _ _
    routedVariableCompactAtomWordRecipeBlocks_four

/-- Under the matching route-shape guard, one target-rank block is exactly
the four compact words of the selected routed-variable equality. -/
theorem RouteShape.routedVariableCompactAtomWordSelection_eq
    (shape : RouteShape) (pair : RouteDescriptor × RouteDescriptor)
    (shapeMatches : shape.Matches pair.2)
    (anchorRank : pair.1.targetPortRank = 2)
    (sameTarget : pair.1.targetVertexIndex = pair.2.targetVertexIndex) :
    predicateListBlocks
        shape.routedVariableCompactAtomWordPredicates
        (shape.routedVariableCompactAtomWordRecipeBlocks.map fun block =>
          RoutedVariableCompactAtomWordCleanup.words
            (block.map (routedVariableCompactAtomRecipeWord
              (descriptorPairTokens pair) true)))
        (descriptorPairTokens pair) =
      if pair.2.targetPortRank ∈ routedVariableCompactTargetRanks then
        routedVariableCompactAtomWordBlock pair.1 pair.2
      else [] := by
  rw [predicateListBlocks_eq]
  unfold RouteShape.routedVariableCompactAtomWordPredicates
    RouteShape.routedVariableCompactAtomWordRecipeBlocks
    routedVariableCompactTargetRanks
  simp only [List.map_cons, List.map_nil,
    Predicate.evalTokens_descriptorPairTokens]
  have guardTrue : (shape.guard .second).evalPair pair = true := by
    rw [shape.evalPair_guard]
    simp [descriptorAt, shapeMatches]
  simp [RouteShape.routedVariableCompactAtomWordPredicate,
    evalPair_all, evalPair_equal, anchorRank, sameTarget, guardTrue,
    shape.cleanup_activeRecipeBlock pair shapeMatches,
    routedVariableCompactTargetRanks, selectTruthBlocks, descriptorAt]
  by_cases rankZero : pair.2.targetPortRank = 0
  · simp [rankZero]
  by_cases rankOne : pair.2.targetPortRank = 1
  · simp [rankZero, rankOne]
  by_cases rankTwo : pair.2.targetPortRank = 2
  · simp [rankZero, rankOne, rankTwo]
  · have rankTwoInt : (pair.2.targetPortRank : Int) ≠ 2 := by
      exact_mod_cast rankTwo
    simp [rankZero, rankOne, rankTwo, rankTwoInt]

theorem RouteShape.routedVariableCompactAtomWordSelection_eq_nil_of_not_matches
    (shape : RouteShape) (pair : RouteDescriptor × RouteDescriptor)
    (notMatches : ¬shape.Matches pair.2) :
    predicateListBlocks
        shape.routedVariableCompactAtomWordPredicates
        (shape.routedVariableCompactAtomWordRecipeBlocks.map fun block =>
          RoutedVariableCompactAtomWordCleanup.words
            (block.map (routedVariableCompactAtomRecipeWord
              (descriptorPairTokens pair) true)))
        (descriptorPairTokens pair) = [] := by
  rw [predicateListBlocks_eq]
  unfold RouteShape.routedVariableCompactAtomWordPredicates
    RouteShape.routedVariableCompactAtomWordRecipeBlocks
    routedVariableCompactTargetRanks
  simp only [List.map_cons, List.map_nil,
    Predicate.evalTokens_descriptorPairTokens]
  have guardFalse : (shape.guard .second).evalPair pair = false := by
    rw [shape.evalPair_guard]
    simp [descriptorAt, notMatches]
  simp [RouteShape.routedVariableCompactAtomWordPredicate,
    evalPair_all, guardFalse, selectTruthBlocks]

theorem RouteShape.routedVariableCompactAtomWordSelection_eq_nil_of_anchor_ne
    (shape : RouteShape) (pair : RouteDescriptor × RouteDescriptor)
    (anchorNe : pair.1.targetPortRank ≠ 2) :
    predicateListBlocks
        shape.routedVariableCompactAtomWordPredicates
        (shape.routedVariableCompactAtomWordRecipeBlocks.map fun block =>
          RoutedVariableCompactAtomWordCleanup.words
            (block.map (routedVariableCompactAtomRecipeWord
              (descriptorPairTokens pair) true)))
        (descriptorPairTokens pair) = [] := by
  have anchorNeInt : (pair.1.targetPortRank : Int) ≠ 2 := by
    exact_mod_cast anchorNe
  rw [predicateListBlocks_eq]
  unfold RouteShape.routedVariableCompactAtomWordPredicates
    RouteShape.routedVariableCompactAtomWordRecipeBlocks
    routedVariableCompactTargetRanks
  simp only [List.map_cons, List.map_nil,
    Predicate.evalTokens_descriptorPairTokens]
  simp [RouteShape.routedVariableCompactAtomWordPredicate,
    evalPair_all, evalPair_equal, anchorNeInt, descriptorAt,
    selectTruthBlocks]

theorem RouteShape.routedVariableCompactAtomWordSelection_eq_nil_of_target_ne
    (shape : RouteShape) (pair : RouteDescriptor × RouteDescriptor)
    (targetNe : pair.1.targetVertexIndex ≠ pair.2.targetVertexIndex) :
    predicateListBlocks
        shape.routedVariableCompactAtomWordPredicates
        (shape.routedVariableCompactAtomWordRecipeBlocks.map fun block =>
          RoutedVariableCompactAtomWordCleanup.words
            (block.map (routedVariableCompactAtomRecipeWord
              (descriptorPairTokens pair) true)))
        (descriptorPairTokens pair) = [] := by
  have targetNeInt :
      (pair.1.targetVertexIndex : Int) ≠ pair.2.targetVertexIndex := by
    exact_mod_cast targetNe
  rw [predicateListBlocks_eq]
  unfold RouteShape.routedVariableCompactAtomWordPredicates
    RouteShape.routedVariableCompactAtomWordRecipeBlocks
    routedVariableCompactTargetRanks
  simp only [List.map_cons, List.map_nil,
    Predicate.evalTokens_descriptorPairTokens]
  simp [RouteShape.routedVariableCompactAtomWordPredicate,
    evalPair_all, evalPair_equal, targetNeInt, descriptorAt,
    selectTruthBlocks]

/-- On any locally shaped inner route, the complete affine recipe family is
exactly the route-shape-independent pair block. -/
theorem routedVariableCompactAtomWords_descriptorPairTokens
    (pair : RouteDescriptor × RouteDescriptor)
    (hasLocalShape :
      _root_.LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine.RouteDescriptor.HasLocalShape
        pair.2) :
    routedVariableCompactAtomWords (descriptorPairTokens pair) =
      routedVariableCompactAtomWordPairBlock pair := by
  rw [routedVariableCompactAtomWords_eq_predicateListBlocks]
  unfold routedVariableCompactAtomWordOutputBlocks
  unfold routedVariableCompactAtomWordPredicates
    routedVariableCompactAtomWordRecipeBlocks
  rw [List.map_flatMap, predicateListBlocks_eq, List.map_flatMap]
  rw [selectTruthBlocks_flatMap]
  · by_cases anchorRank : pair.1.targetPortRank = 2
    · by_cases sameTarget :
          pair.1.targetVertexIndex = pair.2.targetVertexIndex
      · rcases hasLocalShape with ⟨selectedShape, shapeMatches⟩
        rw [flatMap_eq_of_unique
          allRouteShapes
          (fun shape =>
            selectTruthBlocks
              (shape.routedVariableCompactAtomWordRecipeBlocks.map
                fun block =>
                  RoutedVariableCompactAtomWordCleanup.words
                    (block.map (routedVariableCompactAtomRecipeWord
                      (descriptorPairTokens pair) true)))
              (shape.routedVariableCompactAtomWordPredicates.map
                fun predicate =>
                  predicate.evalTokens (descriptorPairTokens pair)))
          selectedShape allRouteShapes_nodup
          (mem_allRouteShapes selectedShape)]
        · rw [← predicateListBlocks_eq]
          rw [selectedShape.routedVariableCompactAtomWordSelection_eq
            pair shapeMatches anchorRank sameTarget]
          simp [routedVariableCompactAtomWordPairBlock,
            anchorRank, sameTarget]
        · intro shape _shapeMember shapeNe
          rw [← predicateListBlocks_eq]
          apply shape.routedVariableCompactAtomWordSelection_eq_nil_of_not_matches
          intro otherMatches
          exact shapeNe (RouteShape.eq_of_matches otherMatches shapeMatches)
      · rw [show routedVariableCompactAtomWordPairBlock pair = [] by
          simp [routedVariableCompactAtomWordPairBlock, sameTarget]]
        apply List.flatMap_eq_nil_iff.mpr
        intro shape shapeMember
        rw [← predicateListBlocks_eq]
        exact shape.routedVariableCompactAtomWordSelection_eq_nil_of_target_ne
          pair sameTarget
    · rw [show routedVariableCompactAtomWordPairBlock pair = [] by
        simp [routedVariableCompactAtomWordPairBlock, anchorRank]]
      apply List.flatMap_eq_nil_iff.mpr
      intro shape shapeMember
      rw [← predicateListBlocks_eq]
      exact shape.routedVariableCompactAtomWordSelection_eq_nil_of_anchor_ne
        pair anchorRank
  · intro shape _shapeMember
    simp [RouteShape.routedVariableCompactAtomWordPredicates,
      RouteShape.routedVariableCompactAtomWordRecipeBlocks]

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
