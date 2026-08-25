/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.BoolSquareRowsMatrixSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankStableLowerSideNumericSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankStableLowerTieBitNumericSemantics

/-! # Numeric rows of equal-coordinate stable carrier comparisons -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankStableLower

theorem tieRows_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    (tieRows (PeriodicCNF.numericRouteDescriptors formula)).words =
      let datums :=
        (routeDescriptorCarrierRankDatumsAtPeriod
          (routeDescriptorStreamGridSize
            (PeriodicCNF.numericRouteDescriptors formula))
          (PeriodicCNF.numericRouteDescriptors formula)).dedup
      datums.map fun first => datums.map (tiePredicate first) := by
  let descriptors := PeriodicCNF.numericRouteDescriptors formula
  let datums :=
    (routeDescriptorCarrierRankDatumsAtPeriod
      (routeDescriptorStreamGridSize descriptors) descriptors).dedup
  change (tieRows descriptors).words =
    datums.map fun first => datums.map (tiePredicate first)
  have sideEq : side descriptors = datums.length := by
    simpa [descriptors, datums] using
      side_numericRouteDescriptors formula wellFormed degree
        isLocal forward nonempty
  have bitsEq : tieBits descriptors =
      datums.flatMap fun first => datums.map (tiePredicate first) := by
    simpa [descriptors, datums] using
      tieBits_numericRouteDescriptors formula wellFormed degree
        isLocal forward nonempty
  calc
    (tieRows descriptors).words =
        (List.replicate datums.length datums.length).splitLengths
          (datums.flatMap fun first =>
            datums.map (tiePredicate first)) := by
      simp only [tieRows]
      rw [sideEq, bitsEq]
    _ = datums.map fun first => datums.map (tiePredicate first) :=
      @List.replicate_splitLengths_flatMap_of_length_eq
        CarrierNodeRankDatum Bool datums
        (fun first => datums.map (tiePredicate first))
        datums.length (by intro; simp)

end CarrierRankStableLower
end LeanTrominoes.PeriodicOrthocrossing
