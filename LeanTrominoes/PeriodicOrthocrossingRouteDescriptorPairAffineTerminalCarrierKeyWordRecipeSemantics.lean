/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierKeyWordRecipeBlockSemantics

/-! # Semantics of the complete terminal carrier-key recipe scan -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open PaddedSupportedCandidateWords
open RouteDescriptorPairCarrierKeyWordRecipes

/-- Interpreting every recipe block of one route shape gives its aligned
terminal candidate template blocks. -/
@[simp] theorem RouteShape.map_map_template_terminalCarrierKeyRecipeBlocks
    (shape : RouteShape) (pair : RouteDescriptor × RouteDescriptor) :
    shape.terminalCarrierKeyRecipeBlocks.map
        (fun block => block.map (Recipe.template pair)) =
      shape.terminalCarrierKeyTemplateBlocks pair := by
  unfold RouteShape.terminalCarrierKeyRecipeBlocks
    RouteShape.terminalCarrierKeyTemplateBlocks
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro tagged _taggedMember
  exact tagged.1.map_map_template_terminalCarrierKeyRecipeBlocks
    pair tagged.2

/-- The complete fixed terminal recipe family interprets to the existing
complete terminal template family. -/
@[simp] theorem map_map_template_terminalCarrierKeyRecipeBlocks
    (pair : RouteDescriptor × RouteDescriptor) :
    terminalCarrierKeyRecipeBlocks.map
        (fun block => block.map (Recipe.template pair)) =
      terminalCarrierKeyTemplateBlocks pair := by
  unfold terminalCarrierKeyRecipeBlocks terminalCarrierKeyTemplateBlocks
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro shape _shapeMember
  exact shape.map_map_template_terminalCarrierKeyRecipeBlocks pair

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
