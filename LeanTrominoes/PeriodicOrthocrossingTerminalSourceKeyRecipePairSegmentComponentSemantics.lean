/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalSourceKeyRecipePairData

/-! # Component semantics of one terminal source-key recipe-pair block -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairSourceKeyRecipePairs

@[simp] theorem Segment.componentRecipeBlock_terminalSourceKeyRecipePairBlock
    (segment : Segment) (segmentIndex : Nat) :
    componentRecipeBlock
        (segment.terminalSourceKeyRecipePairBlock segmentIndex) =
      segment.terminalSourceKeyRecipeBlock segmentIndex := by
  unfold Segment.terminalSourceKeyRecipePairBlock
    Segment.terminalSourceKeyRecipeBlock componentRecipeBlock
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro translate _translateMember
  rfl

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
