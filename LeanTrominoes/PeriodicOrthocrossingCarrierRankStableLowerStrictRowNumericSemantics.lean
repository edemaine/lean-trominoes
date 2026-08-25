/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BoolSquareRowsMatrixSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankStableLowerSideNumericSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankStableLowerStrictBitNumericSemantics

/-! # Numeric rows of strict-lower stable carrier comparisons -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankStableLower

theorem lowerRows_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    (lowerRows (PeriodicCNF.numericRouteDescriptors formula)).words =
      let datums :=
        (routeDescriptorCarrierRankDatumsAtPeriod
          (routeDescriptorStreamGridSize
            (PeriodicCNF.numericRouteDescriptors formula))
          (PeriodicCNF.numericRouteDescriptors formula)).dedup
      datums.map fun first => datums.map (lowerPredicate first) := by
  let descriptors := PeriodicCNF.numericRouteDescriptors formula
  let datums :=
    (routeDescriptorCarrierRankDatumsAtPeriod
      (routeDescriptorStreamGridSize descriptors) descriptors).dedup
  change (lowerRows descriptors).words =
    datums.map fun first => datums.map (lowerPredicate first)
  have sideEq : side descriptors = datums.length := by
    simpa [descriptors, datums] using
      side_numericRouteDescriptors formula wellFormed degree
        isLocal forward nonempty
  have bitsEq : lowerBits descriptors =
      datums.flatMap fun first => datums.map (lowerPredicate first) := by
    simpa [descriptors, datums] using
      lowerBits_numericRouteDescriptors formula wellFormed degree
        isLocal forward nonempty
  calc
    (lowerRows descriptors).words =
        (List.replicate datums.length datums.length).splitLengths
          (datums.flatMap fun first =>
            datums.map (lowerPredicate first)) := by
      simp only [lowerRows]
      rw [sideEq, bitsEq]
    _ = datums.map fun first => datums.map (lowerPredicate first) :=
      @List.replicate_splitLengths_flatMap_of_length_eq
        CarrierNodeRankDatum Bool datums
        (fun first => datums.map (lowerPredicate first))
        datums.length (by intro; simp)

end CarrierRankStableLower
end LeanTrominoes.PeriodicOrthocrossing
