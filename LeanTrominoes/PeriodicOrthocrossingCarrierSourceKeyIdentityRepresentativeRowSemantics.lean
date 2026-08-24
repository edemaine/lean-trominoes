/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyIdentityNumericSelectionSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyRepresentativeRowSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierIdentityRepresentativeRowSemantics

/-! # Numeric-route compact source-key representative rows -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- For valid numeric CNF routes, the compiled compact source-key rows are
exactly the established full-identity representative rows. -/
theorem paddedCarrierSourceKeyRepresentativeRows_eq_identityRepresentativeRows_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    paddedCarrierSourceKeyRepresentativeRows
        (PeriodicCNF.numericRouteDescriptors formula) =
      paddedCarrierIdentityRepresentativeRowsAtPeriod
        (routeDescriptorStreamGridSize
          (PeriodicCNF.numericRouteDescriptors formula))
        (PeriodicCNF.numericRouteDescriptors formula) := by
  rw [paddedCarrierSourceKeyRepresentativeRows_eq_selectedRows,
    paddedCarrierIdentityRepresentativeRows_eq_selectedRows]
  exact
    selectedRows_sourceKeyCandidateStream_eq_identityCandidateStream_numericRouteDescriptors
      formula wellFormed degree isLocal forward nonempty

end LeanTrominoes.PeriodicOrthocrossing
