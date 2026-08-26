/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankCompiledKeyData
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyEqualityFieldNumericSemantics

/-! # Numeric-route semantics of aggregate compiled carrier keys -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankCompiledKey

/-- Bundle the six compiler-facing fields of one semantic carrier key. -/
def ofKey (key : Nat × Nat × Cell) : CarrierRankCompiledKey where
  route := key.1
  segment := key.2.1
  horizontalPositive := key.2.2.1.toNat
  horizontalNegative := (-key.2.2.1).toNat
  verticalPositive := key.2.2.2.toNat
  verticalNegative := (-key.2.2.2).toNat

/-- Bundle the six compiler-facing key fields of one semantic rank datum. -/
def ofDatum (datum : CarrierNodeRankDatum) : CarrierRankCompiledKey :=
  ofKey datum.key

/-- On valid numeric routes, pointwise bundling of the six compiled columns
recovers the corresponding aggregate key of every deduplicated rank datum. -/
theorem values_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    values (PeriodicCNF.numericRouteDescriptors formula) =
      let datums :=
        (routeDescriptorCarrierRankDatumsAtPeriod
          (routeDescriptorStreamGridSize
            (PeriodicCNF.numericRouteDescriptors formula))
          (PeriodicCNF.numericRouteDescriptors formula)).dedup
      datums.map ofDatum := by
  let descriptors := PeriodicCNF.numericRouteDescriptors formula
  let datums :=
    (routeDescriptorCarrierRankDatumsAtPeriod
      (routeDescriptorStreamGridSize descriptors) descriptors).dedup
  have fieldEq (field : CarrierKeyFieldProjector.Field) :
      CarrierRankKeyField.values field descriptors =
        datums.map (CarrierRankKeyField.rankValue field) := by
    simpa [descriptors, datums] using
      CarrierRankKeyEquality.selectedValues_numericRouteDescriptors
        formula wellFormed degree isLocal forward nonempty field
  change values descriptors = datums.map ofDatum
  unfold values
  rw [fieldEq .route, fieldEq .segment,
    fieldEq .horizontalPositive, fieldEq .horizontalNegative,
    fieldEq .verticalPositive, fieldEq .verticalNegative]
  apply List.ext_getElem
  · simp
  · intro index _leftBound rightBound
    have indexLt : index < datums.length := by
      simpa using rightBound
    simp only [List.getElem_map, List.getElem_range]
    simp [indexLt, ofDatum, ofKey,
      CarrierRankKeyField.rankValue]

end CarrierRankCompiledKey
end LeanTrominoes.PeriodicOrthocrossing
