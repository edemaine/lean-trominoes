/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListForall2Append
import LeanTrominoes.PeriodicOrthocrossingTerminalSourceKeyRecipePairAxisMatchSemantics

/-! # Alignment of route-shape terminal source-key recipe pairs -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairSourceKeyRecipePairs
open RouteDescriptorPairFieldTags

theorem RouteShape.terminalSourceKeyRecipePairBlocks_matchNode
    (shape : RouteShape) (pair : RouteDescriptor × RouteDescriptor) :
    List.Forall₂
      (List.Forall₂ (MatchesNode (descriptorPairTokens pair)))
      shape.terminalSourceKeyRecipePairBlocks
      (shape.terminalCarrierNodeTemplateBlocks pair) := by
  unfold RouteShape.terminalSourceKeyRecipePairBlocks
    RouteShape.terminalCarrierNodeTemplateBlocks
  induction (shape.segments .first).zipIdx with
  | nil => simp
  | cons tagged taggedSegments induction =>
      rw [List.flatMap_cons, List.flatMap_cons]
      exact (tagged.1.terminalSourceKeyRecipePairBlocks_matchNode
        pair tagged.2).append induction

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
