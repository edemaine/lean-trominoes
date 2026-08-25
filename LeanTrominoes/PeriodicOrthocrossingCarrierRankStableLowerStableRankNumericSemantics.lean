/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankStableLowerNumericSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankStableLowerRankSemantics

/-! # Stable-rank semantics of the compiled numeric carrier column -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankStableLower

/-- On valid numeric routes, every compiled unary value is the strict lower
rank in its carrier-key fiber under the lexicographic coordinate/presentation
order. -/
theorem ranks_numericRouteDescriptors_eq_stableRankAt
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    ranks (PeriodicCNF.numericRouteDescriptors formula) =
      let datums :=
        (routeDescriptorCarrierRankDatumsAtPeriod
          (routeDescriptorStreamGridSize
            (PeriodicCNF.numericRouteDescriptors formula))
          (PeriodicCNF.numericRouteDescriptors formula)).dedup
      datums.zipIdx.map (stableRankAt datums) := by
  rw [ranks_numericRouteDescriptors formula wellFormed degree
    isLocal forward nonempty]
  exact map_rankAt_eq_stableRankAt _

end CarrierRankStableLower
end LeanTrominoes.PeriodicOrthocrossing
