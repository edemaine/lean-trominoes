/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.SAT.Planar.FiniteRetainedPlanarSAT
import LeanTrominoes.SAT.CNF.FiniteCNFReplacementOffsets
import LeanTrominoes.SAT.CNF.PeriodicCNFPlanarHorizontalRetainedExactOne

/-! # The finite retained pipeline through exact-one conversion -/
namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- The concrete fixed-eight occurrence split of the retained planar-SAT
formula has zero offsets. -/
theorem retainedDrawingEightOccurrenceSplitFormula_zeroOffsets
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (_isLocal : source.incidenceGraph.IsLocal)
    (zero : FiniteCNF.ZeroOffsets source) :
    FiniteCNF.ZeroOffsets (retainedDrawingEightOccurrenceSplitFormula source) := by
  apply PeriodicEightOccurrenceSplit.formula_zeroOffsets
  exact retainedPlanarSATFormula_zero_of_source_zero source wellFormed degree zero

/-- Source-first angular-fan refinement changes the displayed coordinates
but not the finite erased fixed-eight formula. -/
theorem
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula_erase_zeroOffsets
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (isLocal : source.incidenceGraph.IsLocal)
    (zero : FiniteCNF.ZeroOffsets source) :
    FiniteCNF.ZeroOffsets (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
      source).erase := by
  rw [retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula_erase]
  exact retainedDrawingEightOccurrenceSplitFormula_zeroOffsets
    wellFormed degree isLocal zero

/-- The first stable clockwise clause ordering preserves the finite
fixed-eight source. -/
theorem
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula_erase_zeroOffsets
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (isLocal : source.incidenceGraph.IsLocal)
    (zero : FiniteCNF.ZeroOffsets source) :
    FiniteCNF.ZeroOffsets (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula
      source).erase := by
  apply PositionedPeriodicCNF.orderClausesByRouteDirection_erase_zeroOffsets
  exact
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula_erase_zeroOffsets
      wellFormed degree isLocal zero

/-- The whole-source Figure 9 clearance scale leaves the finite erased
formula unchanged. -/
theorem retainedFigureNineClearancePositionedFormula_erase_zeroOffsets
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (isLocal : source.incidenceGraph.IsLocal)
    (zero : FiniteCNF.ZeroOffsets source) :
    FiniteCNF.ZeroOffsets (retainedFigureNineClearancePositionedFormula
      source).erase := by
  simpa only [retainedFigureNineClearancePositionedFormula,
    PositionedPeriodicCNF.erase_scale] using
    (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula_erase_zeroOffsets
      wellFormed degree isLocal zero)

end PeriodicOrthocrossing
end LeanTrominoes

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- The concrete twice-replaced unit-free exact-one endpoint has zero offsets
before its final stable clause ordering. -/
theorem
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula_erase_zeroOffsets
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (graphLocal : source.incidenceGraph.IsLocal)
    (zero : FiniteCNF.ZeroOffsets source) :
    FiniteCNF.ZeroOffsets (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
      source).erase := by
  rw [
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula_erase]
  apply PeriodicOneInThreeNoUnits.formula_zeroOffsets
  apply PeriodicOneInThree.formula_zeroOffsets
  exact retainedFigureNineClearancePositionedFormula_erase_zeroOffsets
    wellFormed degree graphLocal zero

/-- The final stable clockwise clause ordering preserves the finite
unit-free exact-one endpoint. -/
theorem
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormula_erase_zeroOffsets
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (graphLocal : source.incidenceGraph.IsLocal)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    (zero : FiniteCNF.ZeroOffsets source) :
    FiniteCNF.ZeroOffsets ((retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormula
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).erase) := by
  apply PositionedPeriodicCNF.orderClausesByRouteDirection_erase_zeroOffsets
  exact
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula_erase_zeroOffsets
      wellFormed degree graphLocal zero

end PeriodicOrthocrossing
end LeanTrominoes
