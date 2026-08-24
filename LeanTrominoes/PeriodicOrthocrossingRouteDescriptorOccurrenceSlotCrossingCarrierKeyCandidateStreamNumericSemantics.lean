/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorLocalShape
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorSelfIndex
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingCarrierKeyCandidateStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingCarrierKeyStreamSemantics

/-! # Numeric slot-major crossing carrier-key candidates -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorOccurrenceSlotCrossing

open PaddedSupportedLastRepresentativeEqualityRows

/-- Filtering inactive values from the padded numeric descriptor-slot square
gives the exact retained carrier-key scan of all semantic crossings. -/
theorem paddedCrossingCarrierKeyCandidateStream_numericRouteDescriptors
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    (paddedCrossingCarrierKeyCandidateStream
        (PeriodicCNF.numericRouteDescriptors formula)).filterMap
          Candidate.value =
      occurrencePairCarrierKeyScan
        (routeDescriptorOrientedCrossingOccurrencePairs
          (PeriodicCNF.numericRouteDescriptors formula)) := by
  rw [filterMap_paddedCrossingCarrierKeyCandidateStream]
  unfold routeDescriptorOrientedCrossingOccurrencePairs
  exact crossingCarrierKeyActiveValueStream_eq_occurrencePairCarrierKeyScan
    (routeDescriptorStreamGridSize
      (PeriodicCNF.numericRouteDescriptors formula))
    (PeriodicCNF.numericRouteDescriptors formula)
    (PeriodicCNF.numericRouteDescriptors_selfIndexed formula)
    (PeriodicCNF.numericRouteDescriptors_commonGridSize formula nonempty)
    (PeriodicCNF.numericRouteDescriptors_all_hasLocalShape formula forward)

end RouteDescriptorOccurrenceSlotCrossing
end LeanTrominoes.PeriodicOrthocrossing
