/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPrefixTrueCountSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankStableLowerTieRowNumericSemantics

/-! # Numeric presentation-prefix tie counts for stable carrier ranks -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankStableLower

theorem tieCounts_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    tieCounts (PeriodicCNF.numericRouteDescriptors formula) =
      let datums :=
        (routeDescriptorCarrierRankDatumsAtPeriod
          (routeDescriptorStreamGridSize
            (PeriodicCNF.numericRouteDescriptors formula))
          (PeriodicCNF.numericRouteDescriptors formula)).dedup
      datums.zipIdx.map fun entry =>
        ((datums.map (tiePredicate entry.1)).take entry.2).count true := by
  unfold tieCounts DelimitedBinaryWordPrefixTrueCounts.counts
  rw [tieRows_numericRouteDescriptors formula wellFormed degree
    isLocal forward nonempty]
  rw [DelimitedBinaryWordPrefixTrueCounts.countsAux_map]
  rfl

end CarrierRankStableLower
end LeanTrominoes.PeriodicOrthocrossing
