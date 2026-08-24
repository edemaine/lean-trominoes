/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierKeyWordRecipeData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairCarrierKeyWordRecipeTemplateSemantics

/-! # Terminal carrier-key recipe block semantics -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairCarrierKeyWordRecipes

/-- Interpreting one segment's terminal recipes gives its existing semantic
terminal carrier-key template block exactly. -/
@[simp] theorem Segment.map_template_terminalCarrierKeyRecipeBlock
    (segment : Segment) (pair : RouteDescriptor × RouteDescriptor)
    (segmentIndex : Nat) :
    (segment.terminalCarrierKeyRecipeBlock segmentIndex).map
        (Recipe.template pair) =
      segment.terminalCarrierKeyTemplateBlock
        pair segmentIndex := by
  unfold Segment.terminalCarrierKeyRecipeBlock
    Segment.terminalCarrierKeyTemplateBlock
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro translate _translateMember
  rw [List.map_replicate]
  rfl

/-- The duplicated horizontal/vertical recipe blocks likewise interpret to
the two existing aligned template blocks. -/
@[simp] theorem Segment.map_map_template_terminalCarrierKeyRecipeBlocks
    (segment : Segment) (pair : RouteDescriptor × RouteDescriptor)
    (segmentIndex : Nat) :
    (segment.terminalCarrierKeyRecipeBlocks segmentIndex).map
        (fun block => block.map (Recipe.template pair)) =
      segment.terminalCarrierKeyTemplateBlocks
        pair segmentIndex := by
  simp [Segment.terminalCarrierKeyRecipeBlocks,
    Segment.terminalCarrierKeyTemplateBlocks]

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
