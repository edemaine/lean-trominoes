/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyAxisBlockActivesSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierKeyWordRecipeActivationSemantics
import LeanTrominoes.PeriodicOrthocrossingTerminalCarrierKeyAxisValueData

/-! # Structural semantics of terminal carrier-key axis blocks -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairCarrierKeyWordRecipes

private theorem forall₂_append
    {First Second : Type*} {Relation : First → Second → Prop}
    {firstHead firstTail : List First}
    {secondHead secondTail : List Second}
    (head : List.Forall₂ Relation firstHead secondHead)
    (tail : List.Forall₂ Relation firstTail secondTail) :
    List.Forall₂ Relation
      (firstHead ++ firstTail) (secondHead ++ secondTail) := by
  induction head with
  | nil => exact tail
  | cons relation rest induction =>
      exact List.Forall₂.cons relation induction

private theorem forall₂_flatMap
    {Index First Second : Type*}
    {Relation : First → Second → Prop}
    (indices : List Index) (first : Index → List First)
    (second : Index → List Second)
    (pointwise : ∀ index ∈ indices,
      List.Forall₂ Relation (first index) (second index)) :
    List.Forall₂ Relation
      (indices.flatMap first) (indices.flatMap second) := by
  induction indices with
  | nil => exact List.Forall₂.nil
  | cons index indices induction =>
      simp only [List.flatMap_cons]
      exact forall₂_append
        (pointwise index (by simp))
        (induction (fun item member => pointwise item (by simp [member])))

private theorem Segment.recipeBlocks_forall₂_axisBlocks_length
    (segment : Segment) (segmentIndex : Nat) :
    List.Forall₂ (fun block axes => block.length = axes.length)
      (segment.terminalCarrierKeyRecipeBlocks segmentIndex)
      (segment.terminalCarrierKeyRecipeAxisBlocks segmentIndex) := by
  simp [Segment.terminalCarrierKeyRecipeBlocks,
    Segment.terminalCarrierKeyRecipeAxisBlocks]

private theorem RouteShape.recipeBlocks_forall₂_axisBlocks_length
    (shape : RouteShape) :
    List.Forall₂ (fun block axes => block.length = axes.length)
      shape.terminalCarrierKeyRecipeBlocks
      shape.terminalCarrierKeyRecipeAxisBlocks := by
  unfold RouteShape.terminalCarrierKeyRecipeBlocks
    RouteShape.terminalCarrierKeyRecipeAxisBlocks
  apply forall₂_flatMap
  intro tagged _taggedMember
  exact tagged.1.recipeBlocks_forall₂_axisBlocks_length tagged.2

/-- Terminal recipe and explicit axis blocks align pointwise in the complete
fixed route-shape scan. -/
theorem terminalCarrierKeyRecipeBlocks_forall₂_axisBlocks_length :
    List.Forall₂ (fun block axes => block.length = axes.length)
      terminalCarrierKeyRecipeBlocks
      terminalCarrierKeyRecipeAxisBlocks := by
  unfold terminalCarrierKeyRecipeBlocks terminalCarrierKeyRecipeAxisBlocks
  apply forall₂_flatMap
  intro shape _shapeMember
  exact shape.recipeBlocks_forall₂_axisBlocks_length

/-- The compiled terminal recipe activations are exactly the activations
obtained by repeating each predicate bit across its explicit axis block. -/
theorem terminalCarrierKeyExpandedActives_eq_axisBlockActives
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    terminalCarrierKeyExpandedActives tokens =
      FixedAxisUnaryFields.blockActives
        (terminalCarrierKeyActivations tokens)
        terminalCarrierKeyRecipeAxisBlocks := by
  rw [terminalCarrierKeyExpandedActives_eq]
  exact expandedActives_eq_axisBlockActives_of_forall₂_length
    (terminalCarrierKeyActivations tokens)
    terminalCarrierKeyRecipeBlocks_forall₂_axisBlocks_length

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
