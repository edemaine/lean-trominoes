/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingTerminalSourceKeyRecipePairShapeMatchSemantics

/-! # Complete terminal source-key recipe-pair alignment -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairSourceKeyRecipePairs
open RouteDescriptorPairFieldTags

theorem terminalSourceKeyRecipePairBlocks_matchNode
    (pair : RouteDescriptor × RouteDescriptor) :
    List.Forall₂
      (List.Forall₂ (MatchesNode (descriptorPairTokens pair)))
      terminalSourceKeyRecipePairBlocks
      (terminalCarrierNodeTemplateBlocks pair) := by
  unfold terminalSourceKeyRecipePairBlocks
    terminalCarrierNodeTemplateBlocks
  induction allRouteShapes with
  | nil => simp
  | cons shape shapes induction =>
      rw [List.flatMap_cons, List.flatMap_cons]
      exact (shape.terminalSourceKeyRecipePairBlocks_matchNode pair).append
        induction

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
