/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumLookupNumericSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyEqualityCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierRankKeyFieldSemantics
import LeanTrominoes.SignedUnaryStrictLowerSemantics

/-! # Numeric semantics of carrier-rank key fields -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankKeyEquality

open SignedUnaryStrictLower

/-- Every selected carrier-key field is the corresponding column of the
deduplicated numeric rank data. -/
theorem selectedValues_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ [])
    (field : CarrierKeyFieldProjector.Field) :
    CarrierRankKeyField.values field
        (PeriodicCNF.numericRouteDescriptors formula) =
      (routeDescriptorCarrierRankDatumsAtPeriod
        (routeDescriptorStreamGridSize
          (PeriodicCNF.numericRouteDescriptors formula))
        (PeriodicCNF.numericRouteDescriptors formula)).dedup.map
          (CarrierRankKeyField.rankValue field) := by
  rw [CarrierRankKeyField.values_eq_selectedFieldValuesAtPeriod
      field
      (routeDescriptorStreamGridSize
        (PeriodicCNF.numericRouteDescriptors formula))
      (PeriodicCNF.numericRouteDescriptors formula)]
  exact
    CarrierRankDatumLookup.selectedFieldValuesAtPeriod_numericRouteDescriptors
      formula wellFormed degree isLocal forward nonempty
      (CarrierRankKeyField.rankValue field)

theorem fieldBits_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ [])
    (field : CarrierKeyFieldProjector.Field) :
    fieldBits field (PeriodicCNF.numericRouteDescriptors formula) =
      let datums :=
        (routeDescriptorCarrierRankDatumsAtPeriod
          (routeDescriptorStreamGridSize
            (PeriodicCNF.numericRouteDescriptors formula))
          (PeriodicCNF.numericRouteDescriptors formula)).dedup
      matrix datums fun first second =>
        decide (CarrierRankKeyField.rankValue field first =
          CarrierRankKeyField.rankValue field second) := by
  unfold fieldBits
  rw [selectedValues_numericRouteDescriptors formula wellFormed degree
    isLocal forward nonempty field]
  rw [UnaryFieldEqualityRows.equalityBits_eq_flatMap]
  simp [matrix, matrixRows, List.flatMap_map, List.map_map,
    Function.comp_def]

end CarrierRankKeyEquality
end LeanTrominoes.PeriodicOrthocrossing
