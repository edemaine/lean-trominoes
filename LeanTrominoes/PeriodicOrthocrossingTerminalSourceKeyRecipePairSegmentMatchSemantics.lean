/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingTerminalSourceKeyRecipePairMatchSemantics

/-! # Alignment of one segment's terminal source-key recipe pairs -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairSourceKeyRecipePairs
open RouteDescriptorPairFieldTags

theorem Segment.terminalSourceKeyRecipePairBlock_matchesNode
    (segment : Segment) (pair : RouteDescriptor × RouteDescriptor)
    (segmentIndex : Nat) :
    List.Forall₂ (MatchesNode (descriptorPairTokens pair))
      (segment.terminalSourceKeyRecipePairBlock segmentIndex)
      (segment.terminalCarrierNodeTemplateBlock pair segmentIndex) := by
  unfold Segment.terminalSourceKeyRecipePairBlock
    Segment.terminalCarrierNodeTemplateBlock
  induction neighborTranslations with
  | nil => simp
  | cons translate translations induction =>
      simp only [List.flatMap_cons, List.map_cons, List.map_nil,
        List.cons_append]
      apply List.Forall₂.cons
      · exact terminalSourceKeyRecipePair_matchesNode
          pair segmentIndex segment translate .start
      · apply List.Forall₂.cons
        · exact terminalSourceKeyRecipePair_matchesNode
            pair segmentIndex segment translate .finish
        · exact induction

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
