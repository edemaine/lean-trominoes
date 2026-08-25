/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListZipIdxMapSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankStableLowerCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierRankStableLowerCountNumericSemantics
import LeanTrominoes.UnaryAlignedAddSemantics

/-! # Numeric semantics of stable carrier lower ranks -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankStableLower

def rankAt (datums : List CarrierNodeRankDatum)
    (entry : CarrierNodeRankDatum × Nat) : Nat :=
  (datums.map (lowerPredicate entry.1)).count true +
    ((datums.map (tiePredicate entry.1)).take entry.2).count true

/-- On valid numeric routes, the compiled unary column is exactly the stable
same-key lower count, with presentation index breaking coordinate ties. -/
theorem ranks_numericRouteDescriptors
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
      datums.zipIdx.map (rankAt datums) := by
  let descriptors := PeriodicCNF.numericRouteDescriptors formula
  let datums :=
    (routeDescriptorCarrierRankDatumsAtPeriod
      (routeDescriptorStreamGridSize descriptors) descriptors).dedup
  have lowerEq : lowerCounts descriptors =
      datums.map fun first =>
        (datums.map (lowerPredicate first)).count true := by
    simpa [descriptors, datums] using
      lowerCounts_numericRouteDescriptors formula wellFormed degree
        isLocal forward nonempty
  have tieEq : tieCounts descriptors =
      datums.zipIdx.map fun entry =>
        ((datums.map (tiePredicate entry.1)).take entry.2).count true := by
    simpa [descriptors, datums] using
      tieCounts_numericRouteDescriptors formula wellFormed degree
        isLocal forward nonempty
  change UnaryAlignedAddMachine.sums
      (lowerCounts descriptors) (tieCounts descriptors) =
    datums.zipIdx.map (rankAt datums)
  rw [lowerEq, tieEq]
  rw [UnaryAlignedAddMachine.sums_eq_zipWith
    (UnaryAlignedAddMachine.Valid.of_length_eq (by simp))]
  rw [LeanTrominoes.List.zipWith_map_zipIdx]
  rfl

end CarrierRankStableLower
end LeanTrominoes.PeriodicOrthocrossing
