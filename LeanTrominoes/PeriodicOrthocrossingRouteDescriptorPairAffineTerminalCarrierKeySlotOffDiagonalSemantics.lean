/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierKeySlotShapeOffDiagonalSemantics

/-! # Off-diagonal descriptor-pair terminal carrier-key slots -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags
open PaddedSupportedCandidateBlocks

/-- The complete terminal-key shape scan is empty on an off-diagonal
descriptor pair. -/
theorem terminalCarrierKeyActiveValues_eq_nil_of_edgeIndex_ne
    (pair : RouteDescriptor × RouteDescriptor)
    (edgeIndexNe : pair.1.edgeIndex ≠ pair.2.edgeIndex) :
    activeValues
        (terminalCarrierKeyActivations (descriptorPairTokens pair))
        (terminalCarrierKeyTemplateBlocks pair) = [] := by
  unfold terminalCarrierKeyActivations carrierSegmentPredicates
    terminalCarrierKeyTemplateBlocks
  rw [List.map_flatMap, activeValues_flatMap]
  · apply List.flatMap_eq_nil_iff.mpr
    intro shape _shapeMember
    exact shape.terminalCarrierKeyActiveValues_eq_nil_of_edgeIndex_ne
      pair edgeIndexNe
  · intro shape _shapeMember
    simp [RouteShape.carrierSegmentPredicates,
      RouteShape.terminalCarrierKeyTemplateBlocks,
      Segment.carrierAxisPredicates,
      Segment.terminalCarrierKeyTemplateBlocks]

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
