/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingTerminalSourceKeyRecipePairSegmentMatchSemantics

/-! # Alignment of duplicated terminal source-key recipe-pair blocks -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairSourceKeyRecipePairs
open RouteDescriptorPairFieldTags

theorem Segment.terminalSourceKeyRecipePairBlocks_matchNode
    (segment : Segment) (pair : RouteDescriptor × RouteDescriptor)
    (segmentIndex : Nat) :
    List.Forall₂
      (List.Forall₂ (MatchesNode (descriptorPairTokens pair)))
      (segment.terminalSourceKeyRecipePairBlocks segmentIndex)
      (segment.terminalCarrierNodeTemplateBlocks pair segmentIndex) := by
  simp only [Segment.terminalSourceKeyRecipePairBlocks,
    Segment.terminalCarrierNodeTemplateBlocks]
  exact List.Forall₂.cons
    (segment.terminalSourceKeyRecipePairBlock_matchesNode pair segmentIndex)
    (List.Forall₂.cons
      (segment.terminalSourceKeyRecipePairBlock_matchesNode pair segmentIndex)
      List.Forall₂.nil)

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
