/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankStableLowerStrictRowNumericSemantics

/-! # Numeric strict-lower counts for stable carrier ranks -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankStableLower

theorem lowerCounts_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    lowerCounts (PeriodicCNF.numericRouteDescriptors formula) =
      let datums :=
        (routeDescriptorCarrierRankDatumsAtPeriod
          (routeDescriptorStreamGridSize
            (PeriodicCNF.numericRouteDescriptors formula))
          (PeriodicCNF.numericRouteDescriptors formula)).dedup
      datums.map fun first =>
        (datums.map (lowerPredicate first)).count true := by
  unfold lowerCounts DelimitedBinaryWordTrueCounts.counts
    DelimitedBinaryWordTrueCounts.countTrue
  rw [lowerRows_numericRouteDescriptors formula wellFormed degree
    isLocal forward nonempty]
  simp [List.map_map, Function.comp_def]

end CarrierRankStableLower
end LeanTrominoes.PeriodicOrthocrossing
