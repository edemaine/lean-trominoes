/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderAffineTerminalAlternativeAlignment
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderAffineTerminalSourceKeyStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderRecipeWordLength

/-! # Terminal source-key component lengths for carrier order coordinates -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

/-- Each terminal source identity has two adjacent component words, while
each direction-split expression contributes one coordinate value. -/
theorem Segment.terminalSourceKeyRecipeBlock_length_twice_orderExpressionBlock
    (segment : Segment) (segmentIndex : Nat)
    (horizontal increasing : Bool) :
    (segment.terminalSourceKeyRecipeBlock segmentIndex).length =
      2 * (segment.terminalDirectionalOrderExpressionBlock
        horizontal increasing).length := by
  unfold Segment.terminalSourceKeyRecipeBlock
    Segment.terminalDirectionalOrderExpressionBlock
  have aligned : ∀ translations : List Cell,
      (translations.flatMap fun translate =>
        let start := terminalSourceKeyRecipe segmentIndex translate .start
        let finish := terminalSourceKeyRecipe segmentIndex translate .finish
        [start, start, finish, finish]).length =
      2 * (translations.flatMap fun translate =>
        [segment.terminalOrderExpressionForDirection
            horizontal translate .start increasing,
          segment.terminalOrderExpressionForDirection
            horizontal translate .finish increasing]).length := by
    intro translations
    induction translations with
    | nil => rfl
    | cons translate translations induction =>
        simp only [List.flatMap_cons, List.length_append,
          List.length_cons, List.length_nil]
        rw [induction]
        omega
  exact aligned neighborTranslations

/-- The four direction-split source-component blocks of one segment contain
twice as many words as its four coordinate-expression blocks. -/
theorem Segment.terminalDirectionalSourceKeyRecipes_length_twice_expressions
    (segment : Segment) (segmentIndex : Nat) :
    (segment.terminalDirectionalSourceKeyRecipeBlocks
      segmentIndex).flatten.length =
      2 * segment.terminalDirectionalOrderExpressionBlocks.flatten.length := by
  unfold Segment.terminalDirectionalSourceKeyRecipeBlocks
    Segment.terminalDirectionalOrderExpressionBlocks
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil,
    List.length_append]
  have horizontalDecreasing :=
    segment.terminalSourceKeyRecipeBlock_length_twice_orderExpressionBlock
      segmentIndex true false
  have horizontalIncreasing :=
    segment.terminalSourceKeyRecipeBlock_length_twice_orderExpressionBlock
      segmentIndex true true
  have verticalDecreasing :=
    segment.terminalSourceKeyRecipeBlock_length_twice_orderExpressionBlock
      segmentIndex false false
  have verticalIncreasing :=
    segment.terminalSourceKeyRecipeBlock_length_twice_orderExpressionBlock
      segmentIndex false true
  omega

theorem RouteShape.terminalDirectionalSourceKeyRecipes_length_twice_expressions
    (shape : RouteShape) :
    shape.terminalDirectionalSourceKeyRecipeBlocks.flatten.length =
      2 * shape.terminalDirectionalOrderExpressionBlocks.flatten.length := by
  unfold RouteShape.terminalDirectionalSourceKeyRecipeBlocks
    RouteShape.terminalDirectionalOrderExpressionBlocks
  have aligned : ∀ (segments : List Segment) (start : Nat),
      ((segments.zipIdx start).flatMap fun tagged =>
        tagged.1.terminalDirectionalSourceKeyRecipeBlocks
          tagged.2).flatten.length =
      2 * (segments.flatMap
        Segment.terminalDirectionalOrderExpressionBlocks).flatten.length := by
    intro segments start
    induction segments generalizing start with
    | nil => rfl
    | cons segment segments induction =>
        simp only [List.zipIdx_cons, List.flatMap_cons,
          List.flatten_append, List.length_append]
        rw [segment.terminalDirectionalSourceKeyRecipes_length_twice_expressions,
          induction]
        omega
  exact aligned (shape.segments .first) 0

theorem terminalDirectionalSourceKeyRecipes_length_twice_expressions :
    terminalDirectionalSourceKeyRecipeBlocks.flatten.length =
      2 * terminalDirectionalOrderExpressions.length := by
  unfold terminalDirectionalSourceKeyRecipeBlocks
    terminalDirectionalOrderExpressions
    terminalDirectionalOrderExpressionBlocks
  induction allRouteShapes with
  | nil => rfl
  | cons shape shapes induction =>
      simp only [List.flatMap_cons, List.flatten_append,
        List.length_append]
      rw [shape.terminalDirectionalSourceKeyRecipes_length_twice_expressions,
        induction]
      omega

/-- The direction-split terminal source-component stream has exactly two
words per normalized coordinate value. -/
theorem terminalDirectionalSourceKeyGuardedComponentWords_length
    (keepPositive : Bool)
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    (terminalDirectionalSourceKeyGuardedComponentWords tokens).length =
      2 * (terminalDirectionalOrderFields keepPositive tokens).length := by
  unfold terminalDirectionalSourceKeyGuardedComponentWords
    terminalDirectionalOrderFields
  rw [RouteDescriptorPairCarrierKeyWordRecipes.words_length_of_length_eq]
  · rw [normalizedFields_length,
      terminalDirectionalSourceKeyRecipes_length_twice_expressions]
  · rw [List.length_map]
    exact terminalDirectionalSourceKeyRecipeBlocks_length.symm

end RouteDescriptorPairAffine

namespace TerminalDirectionalSourceKeyStream

/-- Terminal source-component and order-value streams remain aligned after
concatenating all descriptor-pair blocks. -/
theorem guardedComponentWords_length_twice_orderFields
    (keepPositive : Bool)
    (pairs : List (RouteDescriptor × RouteDescriptor)) :
    (guardedComponentWords pairs).length =
      2 * (pairs.flatMap fun pair =>
        RouteDescriptorPairAffine.terminalDirectionalOrderFields
          keepPositive
          (RouteDescriptorPairFieldTags.descriptorPairTokens pair)).length := by
  induction pairs with
  | nil => rfl
  | cons pair pairs induction =>
      simp only [guardedComponentWords, List.flatMap_cons,
        List.length_append]
      change
        (RouteDescriptorPairAffine.terminalDirectionalSourceKeyGuardedComponentWords
          (RouteDescriptorPairFieldTags.descriptorPairTokens pair)).length +
            (guardedComponentWords pairs).length = _
      rw [RouteDescriptorPairAffine.terminalDirectionalSourceKeyGuardedComponentWords_length
          keepPositive,
        induction]
      omega

end TerminalDirectionalSourceKeyStream
end LeanTrominoes.PeriodicOrthocrossing
