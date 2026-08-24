/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankHorizontalFieldAlignmentSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankHorizontalFieldData

/-! # Numeric semantics of the selected carrier horizontal field -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankHorizontalField

/-- For valid numeric CNF routes, the compiled source-key lookup is exactly
the selected horizontal field of every deduplicated carrier rank datum. -/
theorem values_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    values (PeriodicCNF.numericRouteDescriptors formula) =
      CarrierRankDatumLookup.selectedFieldValuesAtPeriod
        (routeDescriptorStreamGridSize
          (PeriodicCNF.numericRouteDescriptors formula))
        (PeriodicCNF.numericRouteDescriptors formula)
        (fun datum => if datum.horizontal then 1 else 0) := by
  unfold values CarrierSourceKeyRepresentativeLookup.values
    CarrierRankDatumLookup.selectedFieldValuesAtPeriod
  rw [carrierKeyAxisValuesWithSentinel_numeric_horizontalField
    formula wellFormed degree isLocal forward nonempty]

end CarrierRankHorizontalField
end LeanTrominoes.PeriodicOrthocrossing

end
