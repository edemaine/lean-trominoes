/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderAffineTerminalCandidateCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderAffineTerminalSourceKeyCandidateCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierKeyWordRecipeActivationSemantics

/-! # Alignment of direction-split terminal candidate families -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairCarrierKeyWordRecipes

@[simp] theorem Segment.terminalDirectionalPredicates_length
    (shape : RouteShape) (segment : Segment) :
    (segment.terminalDirectionalPredicates shape).length = 4 := by
  rfl

@[simp] theorem Segment.terminalDirectionalOrderExpressionBlocks_length
    (segment : Segment) :
    segment.terminalDirectionalOrderExpressionBlocks.length = 4 := by
  rfl

@[simp] theorem Segment.terminalDirectionalCarrierKeyRecipeBlocks_length
    (segmentIndex : Nat) (segment : Segment) :
    (segment.terminalDirectionalCarrierKeyRecipeBlocks
      segmentIndex).length = 4 := by
  rfl

@[simp] theorem Segment.terminalDirectionalSourceKeyRecipeBlocks_length
    (segmentIndex : Nat) (segment : Segment) :
    (segment.terminalDirectionalSourceKeyRecipeBlocks
      segmentIndex).length = 4 := by
  rfl

/-- Every direction-split expression block is length-aligned with its
duplicated key-recipe block. -/
theorem Segment.terminalDirectionalOrderExpressionBlockLengths_eq_recipes
    (segment : Segment) (segmentIndex : Nat) :
    segment.terminalDirectionalOrderExpressionBlocks.map List.length =
      (segment.terminalDirectionalCarrierKeyRecipeBlocks segmentIndex).map
        List.length := by
  simp [Segment.terminalDirectionalOrderExpressionBlocks,
    Segment.terminalDirectionalOrderExpressionBlock,
    Segment.terminalDirectionalCarrierKeyRecipeBlocks,
    Segment.terminalCarrierKeyRecipeBlock]

theorem RouteShape.terminalDirectionalOrderExpressionBlockLengths_eq_recipes
    (shape : RouteShape) :
    shape.terminalDirectionalOrderExpressionBlocks.map List.length =
      shape.terminalDirectionalCarrierKeyRecipeBlocks.map List.length := by
  unfold RouteShape.terminalDirectionalOrderExpressionBlocks
    RouteShape.terminalDirectionalCarrierKeyRecipeBlocks
  have aligned : ∀ (segments : List Segment) (start : Nat),
      (segments.flatMap
          Segment.terminalDirectionalOrderExpressionBlocks).map List.length =
        ((segments.zipIdx start).flatMap fun tagged =>
          tagged.1.terminalDirectionalCarrierKeyRecipeBlocks
            tagged.2).map List.length := by
    intro segments start
    induction segments generalizing start with
    | nil => rfl
    | cons segment segments induction =>
        simp only [List.zipIdx_cons, List.flatMap_cons, List.map_append]
        rw [segment.terminalDirectionalOrderExpressionBlockLengths_eq_recipes,
          induction]
  exact aligned (shape.segments .first) 0

theorem terminalDirectionalOrderExpressionBlockLengths_eq_recipes :
    terminalDirectionalOrderExpressionBlocks.map List.length =
      terminalDirectionalCarrierKeyRecipeBlocks.map List.length := by
  unfold terminalDirectionalOrderExpressionBlocks
    terminalDirectionalCarrierKeyRecipeBlocks
  induction allRouteShapes with
  | nil => rfl
  | cons shape shapes induction =>
      simp only [List.flatMap_cons, List.map_append]
      rw [shape.terminalDirectionalOrderExpressionBlockLengths_eq_recipes,
        induction]

@[simp] theorem RouteShape.terminalDirectionalPredicates_length
    (shape : RouteShape) :
    shape.terminalDirectionalPredicates.length =
      shape.terminalDirectionalCarrierKeyRecipeBlocks.length := by
  unfold RouteShape.terminalDirectionalPredicates
    RouteShape.terminalDirectionalCarrierKeyRecipeBlocks
  simp

@[simp] theorem RouteShape.terminalDirectionalOrderExpressionBlocks_length
    (shape : RouteShape) :
    shape.terminalDirectionalOrderExpressionBlocks.length =
      shape.terminalDirectionalCarrierKeyRecipeBlocks.length := by
  unfold RouteShape.terminalDirectionalOrderExpressionBlocks
    RouteShape.terminalDirectionalCarrierKeyRecipeBlocks
  simp

@[simp] theorem RouteShape.terminalDirectionalSourceKeyRecipeBlocks_length
    (shape : RouteShape) :
    shape.terminalDirectionalSourceKeyRecipeBlocks.length =
      shape.terminalDirectionalPredicates.length := by
  unfold RouteShape.terminalDirectionalSourceKeyRecipeBlocks
    RouteShape.terminalDirectionalPredicates
  simp

@[simp] theorem terminalDirectionalPredicates_length :
    terminalDirectionalPredicates.length =
      terminalDirectionalCarrierKeyRecipeBlocks.length := by
  unfold terminalDirectionalPredicates
    terminalDirectionalCarrierKeyRecipeBlocks
  simp

@[simp] theorem terminalDirectionalOrderExpressionBlocks_length :
    terminalDirectionalOrderExpressionBlocks.length =
      terminalDirectionalCarrierKeyRecipeBlocks.length := by
  unfold terminalDirectionalOrderExpressionBlocks
    terminalDirectionalCarrierKeyRecipeBlocks
  simp

@[simp] theorem terminalDirectionalSourceKeyRecipeBlocks_length :
    terminalDirectionalSourceKeyRecipeBlocks.length =
      terminalDirectionalPredicates.length := by
  unfold terminalDirectionalSourceKeyRecipeBlocks
    terminalDirectionalPredicates
  simp

/-- Flattened affine fields and flattened guarded keys have exactly the same
candidate count. -/
@[simp] theorem terminalDirectionalOrderExpressions_length :
    terminalDirectionalOrderExpressions.length =
      terminalDirectionalCarrierKeyRecipeBlocks.flatten.length := by
  unfold terminalDirectionalOrderExpressions
  rw [List.length_flatten, List.length_flatten,
    terminalDirectionalOrderExpressionBlockLengths_eq_recipes]

/-- Compiled direction-split activity has one bit per flattened key recipe. -/
@[simp] theorem terminalDirectionalExpandedActives_eq
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    terminalDirectionalExpandedActives tokens =
      expandedActives
        (terminalDirectionalPredicates.map
          fun predicate => predicate.evalTokens tokens)
        terminalDirectionalCarrierKeyRecipeBlocks := by
  unfold terminalDirectionalExpandedActives predicateListExpandedActives
  rw [predicateListTruthValues_eq]
  apply compiledExpandedActives_eq
  rw [List.length_map]
  exact terminalDirectionalPredicates_length

/-- Compiled source-key component activity repeats each direction predicate
over its doubled recipe block. -/
@[simp] theorem terminalDirectionalSourceKeyExpandedActives_eq
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    terminalDirectionalSourceKeyExpandedActives tokens =
      expandedActives
        (terminalDirectionalPredicates.map
          fun predicate => predicate.evalTokens tokens)
        terminalDirectionalSourceKeyRecipeBlocks := by
  unfold terminalDirectionalSourceKeyExpandedActives
    predicateListExpandedActives
  rw [predicateListTruthValues_eq]
  apply compiledExpandedActives_eq
  rw [List.length_map]
  exact terminalDirectionalSourceKeyRecipeBlocks_length.symm

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
