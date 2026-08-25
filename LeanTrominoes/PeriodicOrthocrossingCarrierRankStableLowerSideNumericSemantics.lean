/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyEqualityFieldNumericSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankStableLowerPredicateData

/-! # Numeric side length of stable carrier-rank matrices -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankStableLower

theorem side_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    side (PeriodicCNF.numericRouteDescriptors formula) =
      (routeDescriptorCarrierRankDatumsAtPeriod
        (routeDescriptorStreamGridSize
          (PeriodicCNF.numericRouteDescriptors formula))
        (PeriodicCNF.numericRouteDescriptors formula)).dedup.length := by
  have valuesEq :=
    CarrierRankKeyEquality.selectedValues_numericRouteDescriptors
      formula wellFormed degree isLocal forward nonempty .route
  have lengths := congrArg List.length valuesEq
  simpa [side] using lengths

end CarrierRankStableLower
end LeanTrominoes.PeriodicOrthocrossing
