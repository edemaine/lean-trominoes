/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumCompiledFirstCrossingNumericSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumCompiledPrefixNumericSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumCompiledSecondCrossingNumericSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumCompiledSuffixNumericSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierRankDatumFieldColumnNumericSemantics

/-! # Numeric semantics of all fifty compiled carrier rank columns -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierRankDatumCompiledFields

/-- The assembled compiler columns are exactly the generic selected rank-scan
columns on valid numeric routes. -/
theorem columns_numericRouteDescriptors_eq_selectedAtPeriod
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    columns (PeriodicCNF.numericRouteDescriptors formula) =
      CarrierRankDatumFieldColumns.selectedAtPeriod
        (routeDescriptorStreamGridSize
          (PeriodicCNF.numericRouteDescriptors formula))
        (PeriodicCNF.numericRouteDescriptors formula) := by
  let descriptors := PeriodicCNF.numericRouteDescriptors formula
  let period := routeDescriptorStreamGridSize descriptors
  rw [columns_eq_groups]
  rw [prefixColumns_numericRouteDescriptors
    formula wellFormed degree isLocal forward nonempty]
  rw [firstCrossingColumns_numericRouteDescriptors
    formula wellFormed degree isLocal forward nonempty]
  rw [secondCrossingColumns_numericRouteDescriptors
    formula wellFormed degree isLocal forward nonempty]
  rw [suffixColumns_numericRouteDescriptors
    formula wellFormed degree isLocal forward nonempty]
  rw [← selectedColumnsFor_all_eq_selectedAtPeriod period descriptors]
  simp [all, selectedColumnsFor, descriptors, period]

/-- Consequently, the assembled compiler returns the exact column-major view
of the stably deduplicated numeric-route carrier rank data. -/
theorem columns_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    columns (PeriodicCNF.numericRouteDescriptors formula) =
      CarrierRankDatumFieldColumns.ofRankDatums
        (routeDescriptorCarrierRankDatumsAtPeriod
          (routeDescriptorStreamGridSize
            (PeriodicCNF.numericRouteDescriptors formula))
          (PeriodicCNF.numericRouteDescriptors formula)).dedup := by
  rw [columns_numericRouteDescriptors_eq_selectedAtPeriod
    formula wellFormed degree isLocal forward nonempty]
  exact CarrierRankDatumFieldColumns.selectedAtPeriod_numericRouteDescriptors
    formula wellFormed degree isLocal forward nonempty

/-- The physical unary output of the assembled compiler is the encoding of
that exact column-major rank scan. -/
theorem encodedColumns_numericRouteDescriptors
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    encodedColumns (PeriodicCNF.numericRouteDescriptors formula) =
      (CarrierRankDatumFieldColumns.ofRankDatums
        (routeDescriptorCarrierRankDatumsAtPeriod
          (routeDescriptorStreamGridSize
            (PeriodicCNF.numericRouteDescriptors formula))
          (PeriodicCNF.numericRouteDescriptors formula)).dedup).flatMap
            UnaryFieldEncoderMachine.unaryFields := by
  rw [encodedColumns_eq_flatMap_columns]
  rw [columns_numericRouteDescriptors
    formula wellFormed degree isLocal forward nonempty]

end CarrierRankDatumCompiledFields
end LeanTrominoes.PeriodicOrthocrossing
