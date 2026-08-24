/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorLocalShape
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorSelfIndex
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingCarrierNodeCandidateStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingCarrierNodeStreamSemantics

/-! # Numeric crossing carrier-node candidate semantics -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open PaddedSupportedLastRepresentativeEqualityRows

/-- Filtering inactive values from the padded numeric descriptor-slot square
gives the exact retained crossing-boundary suffix. -/
theorem paddedCrossingCarrierNodeCandidateStream_numericRouteDescriptors
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    (paddedCrossingCarrierNodeCandidateStream
        (PeriodicCNF.numericRouteDescriptors formula)).filterMap
          Candidate.value =
      (occurrencePairRetainedCrossingRecordScanAtPeriod
        (routeDescriptorStreamGridSize
          (PeriodicCNF.numericRouteDescriptors formula))
        (routeDescriptorOrientedCrossingOccurrencePairsAtPeriod
          (routeDescriptorStreamGridSize
            (PeriodicCNF.numericRouteDescriptors formula))
          (PeriodicCNF.numericRouteDescriptors formula))).flatMap
            crossingRecordCarrierBoundaryNodes := by
  rw [filterMap_paddedCrossingCarrierNodeCandidateStream]
  exact crossingCarrierNodeActiveValueStream_eq_retainedBoundaryScan
    (routeDescriptorStreamGridSize
      (PeriodicCNF.numericRouteDescriptors formula))
    (PeriodicCNF.numericRouteDescriptors formula)
    (PeriodicCNF.numericRouteDescriptors_selfIndexed formula)
    (PeriodicCNF.numericRouteDescriptors_commonGridSize formula nonempty)
    (PeriodicCNF.numericRouteDescriptors_all_hasLocalShape formula forward)

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
