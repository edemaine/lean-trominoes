/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyEqualityNumericSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankOrderStrictLowerNumericSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankStableLowerIntersectionSemantics

/-! # Numeric strict-lower same-key matrix -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankStableLower

theorem lowerBits_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    lowerBits (PeriodicCNF.numericRouteDescriptors formula) =
      let datums :=
        (routeDescriptorCarrierRankDatumsAtPeriod
          (routeDescriptorStreamGridSize
            (PeriodicCNF.numericRouteDescriptors formula))
          (PeriodicCNF.numericRouteDescriptors formula)).dedup
      datums.flatMap fun first => datums.map (lowerPredicate first) := by
  unfold lowerBits
  calc
    intersection
        (CarrierRankKeyEquality.bits
          (PeriodicCNF.numericRouteDescriptors formula))
        (CarrierRankOrderStrictLower.bits
          (PeriodicCNF.numericRouteDescriptors formula)) =
      intersection
        (let datums :=
          (routeDescriptorCarrierRankDatumsAtPeriod
            (routeDescriptorStreamGridSize
              (PeriodicCNF.numericRouteDescriptors formula))
            (PeriodicCNF.numericRouteDescriptors formula)).dedup
         datums.flatMap fun first =>
           datums.map fun second => decide (first.key = second.key))
        (let datums :=
          (routeDescriptorCarrierRankDatumsAtPeriod
            (routeDescriptorStreamGridSize
              (PeriodicCNF.numericRouteDescriptors formula))
            (PeriodicCNF.numericRouteDescriptors formula)).dedup
         datums.flatMap fun first => datums.map fun second =>
           decide (second.orderCoordinate < first.orderCoordinate)) :=
      congrArg₂ intersection
        (CarrierRankKeyEquality.bits_numericRouteDescriptors
          formula wellFormed degree isLocal forward nonempty)
        (CarrierRankOrderStrictLower.bits_numericRouteDescriptors
          formula wellFormed degree isLocal forward nonempty)
    _ = _ := by
      rw [intersection_flatMap]
      rfl

end CarrierRankStableLower
end LeanTrominoes.PeriodicOrthocrossing
