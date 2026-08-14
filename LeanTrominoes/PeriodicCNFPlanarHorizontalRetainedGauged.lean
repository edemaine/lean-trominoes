/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFOneDimensionalGauge
import LeanTrominoes.PeriodicCNFOneDimensionalWrapping
import LeanTrominoes.PeriodicCNFPlanarDeduplicationWrapping
import LeanTrominoes.PeriodicCNFPlanarHorizontalRetainedFormula
import LeanTrominoes.PeriodicCNFPlanarHorizontalRetainedGaugeOccurrences
import LeanTrominoes.PositionedPeriodicCNFOneDimensionalDeduplication

/-!
# One-dimensional gauged retained planar-SAT normalization

Opaque wrapping commutes with anchor normalization.  The canonical variable
gauge is vertically zero on every wrapped occurrence, so applying it before
anchor normalization preserves the horizontal retained formula.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- Erasing the canonically gauged, anchor-normalized retained positioned
formula yields a one-dimensional periodic CNF. -/
theorem
    retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula_erase_isOneDimensional
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (horizontal : formula.incidenceGraph.HasZeroVerticalOffsets) :
    (retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
      formula).erase.IsOneDimensional := by
  let raw := retainedDrawingPeriodicPlanarSATFormula formula
  let wrapped := wrapPeriodicPlanarSATFormula raw
  let gauge := retainedDrawingWrappedPeriodicPlanarSATVariableGauge formula
  have rawNormalizedHorizontal : raw.anchorNormalize.IsOneDimensional := by
    exact retainedDrawingPeriodicPlanarSATFormula_anchorNormalize_isOneDimensional
      isLocal horizontal
  have wrappedNormalizedHorizontal :
      wrapped.anchorNormalize.IsOneDimensional := by
    rw [← wrapPeriodicPlanarSATFormula_anchorNormalize]
    exact PeriodicCNF.wrapPeriodicPlanarSATFormula_isOneDimensional
      rawNormalizedHorizontal
  have gaugeVertical :
      ∀ atom ∈ wrapped.variableOccurrences, (gauge atom).2 = 0 := by
    intro atom atomMember
    exact
      retainedDrawingWrappedPeriodicPlanarSATVariableGauge_vertical_eq_zero_of_mem
        wellFormed degree isLocal horizontal atomMember
  have gaugedNormalizedHorizontal :
      (wrapped.variableGauge gauge).anchorNormalize.IsOneDimensional :=
    PeriodicCNF.variableGauge_anchorNormalize_isOneDimensional
      wrapped gauge wrappedNormalizedHorizontal gaugeVertical
  simpa only [
    retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula,
    PositionedPeriodicCNF.erase_anchorNormalize,
    retainedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula,
    PositionedPeriodicCNF.erase_variableGauge,
    retainedWrappedDrawingPositionedPeriodicPlanarSATFormula_erase]
    using gaugedNormalizedHorizontal

/-- Final literal-list deduplication preserves the horizontal retained
positioned formula. -/
theorem
    retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula_erase_isOneDimensional
    {Variable : Type*} [DecidableEq Variable]
    {formula : PeriodicCNF Variable}
    (wellFormed : formula.incidenceGraph.IsWellFormed)
    (degree : formula.incidenceGraph.DegreeAtMost 3)
    (isLocal : formula.incidenceGraph.IsLocal)
    (horizontal : formula.incidenceGraph.HasZeroVerticalOffsets) :
    (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
      formula).erase.IsOneDimensional := by
  rw [
    retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula_eq]
  exact PositionedPeriodicCNF.deduplicateByLiterals_erase_isOneDimensional
    _
    (retainedAnchorNormalizedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula_erase_isOneDimensional
      wellFormed degree isLocal horizontal)

end PeriodicOrthocrossing
end LeanTrominoes
