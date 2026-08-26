/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListZipIdxMapSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankCompiledKeyNumericSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankGlobalCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierRankStableLowerStableRankNumericSemantics
import LeanTrominoes.UnaryAlignedAddSemantics

/-! # Numeric semantics of global key-major stable carrier ranks -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankGlobal

/-- Global rank of one indexed datum: its dedup-last-ordered aggregate-key
block start plus its stable geometric rank within that key. -/
def rankAt (datums : List CarrierNodeRankDatum)
    (entry : CarrierNodeRankDatum × Nat) : Nat :=
  LastOccurrenceBlockStarts.blockStart
      (datums.map CarrierRankCompiledKey.ofDatum)
      (CarrierRankCompiledKey.ofDatum entry.1) +
    CarrierRankStableLower.stableRankAt datums entry

/-- On valid numeric routes, the compiled unary column is exactly the global
key-block/stable-coordinate rank of every deduplicated carrier datum. -/
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
  change UnaryAlignedAddMachine.sums
      (CarrierRankKeyBlockStarts.starts descriptors)
      (CarrierRankStableLower.ranks descriptors) =
    datums.zipIdx.map (rankAt datums)
  rw [UnaryAlignedAddMachine.sums_eq_zipWith
    (CarrierRankGlobalValidity.valid descriptors)]
  rw [CarrierRankKeyBlockStarts.starts_eq_lastOccurrenceBlockStarts,
    CarrierRankCompiledKey.values_numericRouteDescriptors
      formula wellFormed degree isLocal forward nonempty,
    CarrierRankStableLower.ranks_numericRouteDescriptors_eq_stableRankAt
      formula wellFormed degree isLocal forward nonempty]
  unfold LastOccurrenceBlockStarts.starts
  rw [List.map_map, LeanTrominoes.List.zipWith_map_zipIdx]
  rfl

end CarrierRankGlobal
end LeanTrominoes.PeriodicOrthocrossing
