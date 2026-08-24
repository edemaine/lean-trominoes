/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierKeyCandidateStreamData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierKeyRowsData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingCarrierKeyCandidateStreamNumericSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierKeyCandidateStreamSemantics

/-! # Numeric semantics of complete padded carrier-key candidates -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PaddedSupportedLastRepresentativeEqualityRows

/-- Removing inactive slots from the complete padded numeric stream gives
the exact terminal-prefix/crossing candidate order used by retained carrier
selection. -/
theorem paddedCarrierKeyCandidateStream_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    (paddedCarrierKeyCandidateStream
        (PeriodicCNF.numericRouteDescriptors formula)).filterMap
          Candidate.value =
      routeDescriptorCarrierKeyCandidatesAtPeriod
        (routeDescriptorStreamGridSize
          (PeriodicCNF.numericRouteDescriptors formula))
        (PeriodicCNF.numericRouteDescriptors formula) := by
  have terminalEq :=
    RouteDescriptorPairAffine.paddedTerminalCarrierKeyCandidateStream_numericRouteDescriptors
      formula wellFormed degree isLocal forward
  have crossingEq :=
    RouteDescriptorOccurrenceSlotCrossing.paddedCrossingCarrierKeyCandidateStream_numericRouteDescriptors
      formula forward nonempty
  unfold paddedCarrierKeyCandidateStream
    paddedTerminalCarrierKeyCandidateStream
  rw [List.filterMap_append, terminalEq, crossingEq]
  rfl

end LeanTrominoes.PeriodicOrthocrossing
