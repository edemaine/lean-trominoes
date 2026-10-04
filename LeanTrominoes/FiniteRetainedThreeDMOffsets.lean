/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.FiniteRetainedFinalOffsets
import LeanTrominoes.FinitePlanarThreeDMOffsets
import LeanTrominoes.PeriodicCNFPlanarRetainedPolarityNormalizedRibbonThreeDM

/-! # The retained finite source produces zero-offset planar 3DM -/
namespace LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivision

theorem paddedPeriodicThreeDMProblem_zeroOffsets {V : Type*} [DecidableEq V]
    (source : PositionedPeriodicCNF V) (placement : PeriodicVariablePlacement V)
    (routes : PositionedPeriodicCNF.IncidenceRoutes) (zero : FiniteCNF.ZeroOffsets source.erase) :
    (paddedPeriodicThreeDMProblem source placement routes).ZeroOffsets := by
  apply PeriodicPlanarOneInThreeToThreeDM.normalizedProblem_zeroOffsets
  simpa only [PositionedPeriodicCNF.erase_scale] using formula_erase_zeroOffsets placement routes zero
end LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivision

namespace LeanTrominoes.PeriodicOrthocrossing
local instance {V : Type*} [DecidableEq V] :
    DecidableEq (OneInThreeNoUnitVariable (PeriodicPlanarOneInThreeThreeRawVariable V)) :=
  PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

theorem retainedOrderedFixedEightPolarityNormalizedPaddedPeriodicThreeDMProblem_zeroOffsets
    {V : Type*} [DecidableEq V] (source : PeriodicCNF V)
    (sourceLocal : source.IsLocal) (width : source.WidthAtMost 3)
    (occurrences : source.OccurrencesAtMost 3) (nonempty : ∀ clause∈source.clauses,clause≠[])
    (zero : FiniteCNF.ZeroOffsets source) :
    (retainedOrderedFixedEightPolarityNormalizedPaddedPeriodicThreeDMProblem source
      sourceLocal width occurrences nonempty).ZeroOffsets := by
  apply PeriodicOneInThreePolarityNormalizationRouteSubdivision.paddedPeriodicThreeDMProblem_zeroOffsets
  exact retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula_erase_zeroOffsets
    (PeriodicCNF.incidenceGraph_isWellFormed source)
    (PeriodicCNF.incidenceGraph_degreeAtMost width occurrences)
    (zeroOffsetGraph_isLocal _ (FiniteCNF.incidenceGraph_zero source zero))
    sourceLocal width occurrences nonempty zero
end LeanTrominoes.PeriodicOrthocrossing
