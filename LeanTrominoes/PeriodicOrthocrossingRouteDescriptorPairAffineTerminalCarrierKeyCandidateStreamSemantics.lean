/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateBlockActivity
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierKeySlotStreamSemantics

/-! # Numeric padded terminal carrier-key candidate semantics -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

open PaddedSupportedCandidateBlocks
open PaddedSupportedLastRepresentativeEqualityRows

/-- Filtering inactive option slots from the padded numeric descriptor-square
candidate stream gives its exact semantic terminal-key prefix. -/
theorem paddedTerminalCarrierKeyCandidateStream_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal) :
    (((PeriodicCNF.numericRouteDescriptors formula) ×ˢ
          (PeriodicCNF.numericRouteDescriptors formula)).flatMap
        paddedTerminalCarrierKeyCandidates).filterMap Candidate.value =
      occurrenceTerminalCarrierKeys
        (routeDescriptorNeighborOccurrences
          (PeriodicCNF.numericRouteDescriptors formula)) := by
  unfold paddedTerminalCarrierKeyCandidates
  rw [filterMap_value_flatMap_candidates]
  exact terminalCarrierKeyActiveValueStream_numericRouteDescriptors
    formula wellFormed degree isLocal forward

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
