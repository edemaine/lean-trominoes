/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierNodeCandidateStreamData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingCarrierNodeNumericSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierNodeStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorRetainedCarrierBitData

/-! # Exact semantics of complete padded carrier-node candidates -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PaddedSupportedLastRepresentativeEqualityRows

/-- Compacting the complete padded numeric candidate stream recovers the
exact retained terminal-and-crossing carrier-node stream. -/
theorem paddedCarrierNodeCandidateStream_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    (paddedCarrierNodeCandidateStream
        (PeriodicCNF.numericRouteDescriptors formula)).filterMap
          Candidate.value =
      routeDescriptorRetainedCarrierNodesAtPeriod
        (routeDescriptorStreamGridSize
          (PeriodicCNF.numericRouteDescriptors formula))
        (PeriodicCNF.numericRouteDescriptors formula) := by
  unfold paddedCarrierNodeCandidateStream
  rw [List.filterMap_append]
  rw [RouteDescriptorPairAffine.paddedTerminalCarrierNodeCandidateStream_numericRouteDescriptors
      formula wellFormed degree isLocal forward]
  rw [RouteDescriptorOccurrenceSlotCrossing.paddedCrossingCarrierNodeCandidateStream_numericRouteDescriptors
      formula forward nonempty]
  rfl

end LeanTrominoes.PeriodicOrthocrossing
