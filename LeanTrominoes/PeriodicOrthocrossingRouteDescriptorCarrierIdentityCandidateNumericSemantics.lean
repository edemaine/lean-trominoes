/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierIdentityCandidateStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierRankDatumCandidateStreamSemantics

/-! # Numeric-route semantics of padded carrier identities -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PaddedSupportedLastRepresentativeEqualityRows

/-- For numeric CNF routes, compacting the identity candidates gives exactly
the identity projection of the established retained rank-data stream. -/
theorem paddedCarrierIdentityCandidateStream_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    (paddedCarrierIdentityCandidateStreamAtPeriod
        (routeDescriptorStreamGridSize
          (PeriodicCNF.numericRouteDescriptors formula))
        (PeriodicCNF.numericRouteDescriptors formula)).filterMap
          Candidate.value =
      (routeDescriptorCarrierRankDatumsAtPeriod
        (routeDescriptorStreamGridSize
          (PeriodicCNF.numericRouteDescriptors formula))
        (PeriodicCNF.numericRouteDescriptors formula)).map
          CarrierNodeRankDatum.identity := by
  rw [paddedCarrierIdentityCandidateStream_filterMap]
  rw [paddedCarrierRankDatumCandidateStream_numericRouteDescriptors
    formula wellFormed degree isLocal forward nonempty]

end LeanTrominoes.PeriodicOrthocrossing
