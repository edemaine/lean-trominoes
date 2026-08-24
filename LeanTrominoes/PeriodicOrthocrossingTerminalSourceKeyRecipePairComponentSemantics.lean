/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingTerminalSourceKeyRecipePairShapeComponentSemantics

/-! # Component semantics of terminal source-key recipe pairs -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairSourceKeyRecipePairs

@[simp] theorem componentRecipeBlocks_terminalSourceKeyRecipePairBlocks :
    componentRecipeBlocks terminalSourceKeyRecipePairBlocks =
      terminalSourceKeyRecipeBlocks := by
  unfold terminalSourceKeyRecipePairBlocks terminalSourceKeyRecipeBlocks
    componentRecipeBlocks
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro shape _shapeMember
  exact shape.componentRecipeBlocks_terminalSourceKeyRecipePairBlocks

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
