/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingTerminalSourceKeyRecipePairAxisComponentSemantics

/-! # Component semantics of route-shape terminal recipe-pair blocks -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairSourceKeyRecipePairs

@[simp] theorem RouteShape.componentRecipeBlocks_terminalSourceKeyRecipePairBlocks
    (shape : RouteShape) :
    componentRecipeBlocks shape.terminalSourceKeyRecipePairBlocks =
      shape.terminalSourceKeyRecipeBlocks := by
  unfold RouteShape.terminalSourceKeyRecipePairBlocks
    RouteShape.terminalSourceKeyRecipeBlocks componentRecipeBlocks
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro tagged _taggedMember
  exact tagged.1.componentRecipeBlocks_terminalSourceKeyRecipePairBlocks
    tagged.2

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
