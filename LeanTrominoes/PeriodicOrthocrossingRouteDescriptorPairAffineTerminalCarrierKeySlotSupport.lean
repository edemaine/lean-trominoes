/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierKeySlotData

/-! # Support tags of terminal carrier-key templates -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

open PaddedSupportedCandidateBlocks

/-- Every fixed terminal template is tagged supported. -/
theorem terminalCarrierKeyTemplateBlocks_supported_true
    (pair : RouteDescriptor × RouteDescriptor)
    (template : Template CarrierKey)
    (member : template ∈
      (terminalCarrierKeyTemplateBlocks pair).flatten) :
    template.supported = true := by
  unfold terminalCarrierKeyTemplateBlocks at member
  rw [List.mem_flatten] at member
  rcases member with ⟨block, blockMember, templateMember⟩
  rw [List.mem_flatMap] at blockMember
  rcases blockMember with ⟨shape, _shapeMember, blockMember⟩
  unfold RouteShape.terminalCarrierKeyTemplateBlocks at blockMember
  rw [List.mem_flatMap] at blockMember
  rcases blockMember with ⟨tagged, _taggedMember, blockMember⟩
  unfold Segment.terminalCarrierKeyTemplateBlocks at blockMember
  simp only [List.mem_cons, List.not_mem_nil, or_false, or_self]
    at blockMember
  subst block
  unfold Segment.terminalCarrierKeyTemplateBlock at templateMember
  rw [List.mem_flatMap] at templateMember
  rcases templateMember with
    ⟨translate, _translateMember, templateMember⟩
  have templateEq := (List.mem_replicate.mp templateMember).2
  subst template
  rfl

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
