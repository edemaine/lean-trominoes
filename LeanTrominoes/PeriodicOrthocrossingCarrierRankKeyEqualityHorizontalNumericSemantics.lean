/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyEqualityFieldNumericSemantics
import LeanTrominoes.SignedUnaryEqualitySemantics

/-! # Numeric semantics of carrier-key horizontal equality -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankKeyEquality

theorem horizontalBits_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    horizontalBits (PeriodicCNF.numericRouteDescriptors formula) =
      let datums :=
        (routeDescriptorCarrierRankDatumsAtPeriod
          (routeDescriptorStreamGridSize
            (PeriodicCNF.numericRouteDescriptors formula))
          (PeriodicCNF.numericRouteDescriptors formula)).dedup
      SignedUnaryStrictLower.matrix datums fun first second =>
        decide (first.key.2.2.1 = second.key.2.2.1) := by
  unfold horizontalBits
  rw [selectedValues_numericRouteDescriptors formula wellFormed degree
      isLocal forward nonempty .horizontalPositive,
    selectedValues_numericRouteDescriptors formula wellFormed degree
      isLocal forward nonempty .horizontalNegative]
  change SignedUnaryEquality.equalityBits
      (List.map (fun datum : CarrierNodeRankDatum =>
        datum.key.2.2.1.toNat) _)
      (List.map (fun datum : CarrierNodeRankDatum =>
        (-datum.key.2.2.1).toNat) _) = _
  exact SignedUnaryEquality.equalityBits_mapped_magnitudes _
    fun datum : CarrierNodeRankDatum => datum.key.2.2.1

end CarrierRankKeyEquality
end LeanTrominoes.PeriodicOrthocrossing
