/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingTerminalSourceKeyRecipePairSegmentComponentSemantics

/-! # Component semantics of duplicated terminal recipe-pair blocks -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairSourceKeyRecipePairs

@[simp] theorem Segment.componentRecipeBlocks_terminalSourceKeyRecipePairBlocks
    (segment : Segment) (segmentIndex : Nat) :
    componentRecipeBlocks
        (segment.terminalSourceKeyRecipePairBlocks segmentIndex) =
      segment.terminalSourceKeyRecipeBlocks segmentIndex := by
  simp [componentRecipeBlocks,
    Segment.terminalSourceKeyRecipePairBlocks,
    Segment.terminalSourceKeyRecipeBlocks]

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
