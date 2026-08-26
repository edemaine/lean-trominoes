/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListMapIdxOfSelfBEq
import LeanTrominoes.PeriodicOrthocrossingCarrierRankGlobalEnumerationSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankGlobalIndexSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankGlobalNumericSemantics

/-! # Global carrier ranks form a permutation -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankGlobal

/-- Semantic global ranks enumerate exactly `0, ..., n - 1`. -/
theorem rankAt_values_perm_range (datums : List CarrierNodeRankDatum) :
    (datums.zipIdx.map (rankAt datums)).Perm (List.range datums.length) := by
  letI : BEq (CarrierNodeRankDatum × Nat) := instBEqOfDecidableEq
  have enumerationRanks :
      (enumeration datums).map (rankAt datums) =
        List.range (enumeration datums).length := by
    calc
      (enumeration datums).map (rankAt datums) =
          (enumeration datums).map fun entry =>
            @List.idxOf (CarrierNodeRankDatum × Nat)
              instBEqOfDecidableEq entry (enumeration datums) := by
        apply List.map_congr_left
        intro entry entryMember
        exact rankAt_eq_idxOf_enumeration datums entry
          ((mem_enumeration_iff datums entry).mp entryMember)
      _ = List.range (enumeration datums).length :=
        List.map_idxOf_self_eq_range_beq
          (enumeration datums) (enumeration_nodup datums)
  have rankedPermutation :=
    (enumeration_perm_zipIdx datums).map (rankAt datums)
  rw [enumerationRanks] at rankedPermutation
  have enumerationLength :
      (enumeration datums).length = datums.length := by
    simpa using (enumeration_perm_zipIdx datums).length_eq
  simpa [enumerationLength] using rankedPermutation.symm

/-- On numeric route descriptors, the compiled unary global-rank column is
a permutation of its complete canonical index range. -/
theorem ranks_perm_range_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    (ranks (PeriodicCNF.numericRouteDescriptors formula)).Perm
      (List.range
        (ranks (PeriodicCNF.numericRouteDescriptors formula)).length) := by
  let descriptors := PeriodicCNF.numericRouteDescriptors formula
  let datums :=
    (routeDescriptorCarrierRankDatumsAtPeriod
      (routeDescriptorStreamGridSize descriptors) descriptors).dedup
  rw [ranks_numericRouteDescriptors
    formula wellFormed degree isLocal forward nonempty]
  simpa only [List.length_map, List.length_zipIdx] using
    rankAt_values_perm_range datums

end CarrierRankGlobal
end LeanTrominoes.PeriodicOrthocrossing
