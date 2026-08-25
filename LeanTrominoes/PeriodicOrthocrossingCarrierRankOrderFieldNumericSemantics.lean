/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderRepresentativeLookupNumericSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumLookupNumericSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderFieldData

/-! # Numeric semantics of selected carrier order-coordinate fields -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankOrderField

/-- On valid numeric routes, either compiled signed magnitude is exactly the
corresponding field of every deduplicated carrier rank datum. -/
theorem values_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ [])
    (keepPositive : Bool) :
    values keepPositive (PeriodicCNF.numericRouteDescriptors formula) =
      CarrierRankDatumLookup.selectedFieldValuesAtPeriod
        (routeDescriptorStreamGridSize
          (PeriodicCNF.numericRouteDescriptors formula))
        (PeriodicCNF.numericRouteDescriptors formula)
        (carrierRankOrderField keepPositive) := by
  unfold values
  rw [CarrierOrderRepresentativeLookup.values_numericRouteDescriptors
    formula wellFormed degree isLocal forward nonempty keepPositive]
  rw [CarrierRankDatumLookup.selectedFieldValuesAtPeriod_numericRouteDescriptors
    formula wellFormed degree isLocal forward nonempty
    (carrierRankOrderField keepPositive)]

end CarrierRankOrderField
end LeanTrominoes.PeriodicOrthocrossing
