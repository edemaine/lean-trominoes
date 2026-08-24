/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PaddedSupportedCandidateActiveValueMapSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierIdentityCandidateStreamMapSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyAxisNumericHorizontalSemantics

/-! # Alignment of numeric carrier axes with rank horizontal fields -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing

open PaddedSupportedLastRepresentativeEqualityRows

/-- The sentinel-completed carrier-key axis stream is exactly the aligned
horizontal field of the padded carrier rank-datum identities. -/
theorem carrierKeyAxisValuesWithSentinel_numeric_horizontalField
    {Variable : Type} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (forward : formula.IsForwardLocal)
    (nonempty : PeriodicCNF.incidencesWithMetadata formula ≠ []) :
    CarrierKeyAxisStream.valuesWithSentinel
        (PeriodicCNF.numericRouteDescriptors formula) =
      CarrierRankDatumLookup.fieldValuesWithSentinelAtPeriod
        (routeDescriptorStreamGridSize
          (PeriodicCNF.numericRouteDescriptors formula))
        (PeriodicCNF.numericRouteDescriptors formula)
        (fun datum => if datum.horizontal then 1 else 0) := by
  unfold CarrierKeyAxisStream.valuesWithSentinel
    CarrierRankDatumLookup.fieldValuesWithSentinelAtPeriod
  rw [carrierKeyAxisValues_numeric_horizontalField
    formula wellFormed degree isLocal forward nonempty]
  rw [paddedCarrierIdentityCandidateStreamAtPeriod_eq_mapActiveValue]
  rw [values_map_mapActiveValue]
  simp [List.map_map, Function.comp_def]

end LeanTrominoes.PeriodicOrthocrossing

end
