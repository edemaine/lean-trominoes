/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyIdentitySelectionSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierNodeCandidateStreamSemantics

/-! # Numeric-route compact source-key selection semantics -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PaddedSupportedLastRepresentativeEqualityRows

/-- For valid numeric CNF routes, compact source keys retain exactly the
representatives selected by full reversible carrier identities. -/
theorem selectedRows_sourceKeyCandidateStream_eq_identityCandidateStream_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    selectedRows
        (paddedCarrierSourceKeyCandidateStream
          (PeriodicCNF.numericRouteDescriptors formula)) =
      selectedRows
        (paddedCarrierIdentityCandidateStreamAtPeriod
          (routeDescriptorStreamGridSize
            (PeriodicCNF.numericRouteDescriptors formula))
          (PeriodicCNF.numericRouteDescriptors formula)) := by
  apply
    selectedRows_sourceKeyCandidateStream_eq_identityCandidateStream_of_filterMap
  exact paddedCarrierNodeCandidateStream_numericRouteDescriptors
    formula wellFormed degree isLocal forward nonempty

end LeanTrominoes.PeriodicOrthocrossing
