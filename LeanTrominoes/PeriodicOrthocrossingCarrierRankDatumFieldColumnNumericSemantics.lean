/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumFieldColumnData
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumLookupNumericSemantics

/-! # Numeric-route selected carrier rank field columns -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankDatumFieldColumns

/-- Compact representative lookup produces all fifty downstream fields of
the exact stably deduplicated numeric-route rank data. -/
theorem selectedAtPeriod_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    selectedAtPeriod
        (routeDescriptorStreamGridSize
          (PeriodicCNF.numericRouteDescriptors formula))
        (PeriodicCNF.numericRouteDescriptors formula) =
      ofRankDatums
        (routeDescriptorCarrierRankDatumsAtPeriod
          (routeDescriptorStreamGridSize
            (PeriodicCNF.numericRouteDescriptors formula))
          (PeriodicCNF.numericRouteDescriptors formula)).dedup := by
  unfold selectedAtPeriod ofRankDatums
  apply List.map_congr_left
  intro fieldIndex _fieldIndexMember
  exact CarrierRankDatumLookup.selectedFieldValuesAtPeriod_numericRouteDescriptors
    formula wellFormed degree isLocal forward nonempty
    (fun datum => datum.scanUnaryFields.getD fieldIndex 0)

end CarrierRankDatumFieldColumns
end LeanTrominoes.PeriodicOrthocrossing
