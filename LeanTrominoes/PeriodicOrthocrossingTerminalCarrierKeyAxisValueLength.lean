/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierKeyWordRecipeActivationSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairCarrierKeyWordRecipeActivationLength
import LeanTrominoes.PeriodicOrthocrossingTerminalCarrierKeyAxisValueData

/-! # Alignment lengths of padded terminal axis values -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairCarrierKeyWordRecipes

private theorem flatMap_flatten_length_congr
    {Index First Second : Type*} (indices : List Index)
    (first : Index → List (List First))
    (second : Index → List (List Second))
    (pointwise : ∀ index ∈ indices,
      (first index).flatten.length =
        (second index).flatten.length) :
    (indices.flatMap first).flatten.length =
      (indices.flatMap second).flatten.length := by
  induction indices with
  | nil => rfl
  | cons index indices induction =>
      simp only [List.flatMap_cons, List.flatten_append,
        List.length_append]
      rw [pointwise index (by simp),
        induction (fun item member => pointwise item (by simp [member]))]

private theorem Segment.terminalCarrierKeyRecipeAxisBlocks_flatten_length
    (segment : Segment) (segmentIndex : Nat) :
    (segment.terminalCarrierKeyRecipeAxisBlocks
        segmentIndex).flatten.length =
      (segment.terminalCarrierKeyRecipeBlocks
        segmentIndex).flatten.length := by
  simp [Segment.terminalCarrierKeyRecipeAxisBlocks,
    Segment.terminalCarrierKeyRecipeBlocks]

private theorem RouteShape.terminalCarrierKeyRecipeAxisBlocks_flatten_length
    (shape : RouteShape) :
    shape.terminalCarrierKeyRecipeAxisBlocks.flatten.length =
      shape.terminalCarrierKeyRecipeBlocks.flatten.length := by
  unfold RouteShape.terminalCarrierKeyRecipeAxisBlocks
    RouteShape.terminalCarrierKeyRecipeBlocks
  apply flatMap_flatten_length_congr
  intro tagged _taggedMember
  exact tagged.1.terminalCarrierKeyRecipeAxisBlocks_flatten_length
    tagged.2

/-- The fixed axis word has exactly one bit per flattened terminal recipe. -/
theorem terminalCarrierKeyRecipeAxes_length :
    terminalCarrierKeyRecipeAxes.length =
      terminalCarrierKeyRecipeBlocks.flatten.length := by
  unfold terminalCarrierKeyRecipeAxes
    terminalCarrierKeyRecipeAxisBlocks terminalCarrierKeyRecipeBlocks
  apply flatMap_flatten_length_congr
  intro shape _shapeMember
  exact shape.terminalCarrierKeyRecipeAxisBlocks_flatten_length

/-- Every runtime terminal activation word aligns with the fixed axis word. -/
theorem terminalCarrierKeyExpandedActives_axis_length
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    (terminalCarrierKeyExpandedActives tokens).length =
      terminalCarrierKeyRecipeAxes.length := by
  rw [terminalCarrierKeyExpandedActives_eq,
    expandedActives_length_of_length_eq]
  · exact terminalCarrierKeyRecipeAxes_length.symm
  · exact terminalCarrierKeyActivations_length tokens

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
