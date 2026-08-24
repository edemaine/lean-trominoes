/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorLocalShape
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorSegmentGeometry
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierKeySlotDiagonalSemantics

/-! # Numeric diagonal terminal carrier-key slot semantics -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

open RouteDescriptorPairFieldTags
open PaddedSupportedCandidateBlocks

/-- Every listed numeric route descriptor contributes its exact semantic
terminal-key block on the diagonal of the descriptor square. -/
theorem terminalCarrierKeyActiveValues_numeric_diagonal
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (descriptor : RouteDescriptor)
    (descriptorMember :
      descriptor ∈ PeriodicCNF.numericRouteDescriptors formula) :
    activeValues
        (terminalCarrierKeyActivations
          (descriptorPairTokens (descriptor, descriptor)))
        (terminalCarrierKeyTemplateBlocks (descriptor, descriptor)) =
      occurrenceTerminalCarrierKeys
        descriptor.selfIndexedNeighborOccurrences := by
  apply terminalCarrierKeyActiveValues_diagonal descriptor
  · exact PeriodicCNF.numericRouteDescriptors_all_hasLocalShape
      formula forward descriptor descriptorMember
  · intro segment segmentMember
    exact PeriodicCNF.numericRouteDescriptor_segment_axisAligned
      formula wellFormed degree isLocal descriptorMember segmentMember

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
