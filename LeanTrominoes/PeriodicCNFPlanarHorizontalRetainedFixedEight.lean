/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarHorizontalRetainedGauged
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFigureNineClearance
import LeanTrominoes.PeriodicEightOccurrenceSplitOneDimensional
import LeanTrominoes.PositionedPeriodicCNFOneDimensionalOrdering

/-!
# One-dimensional retained fixed-eight source

The concrete retained formula remains one-dimensional through fixed-eight
occurrence splitting, the first stable clause-direction ordering, and the
coordinate refinement that reserves clearance for the Figure 9 gadgets.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- The concrete fixed-eight occurrence split of the retained planar-SAT
formula remains one-dimensional. -/
theorem retainedDrawingEightOccurrenceSplitFormula_isOneDimensional
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (isLocal : source.incidenceGraph.IsLocal)
    (horizontal : source.incidenceGraph.HasZeroVerticalOffsets) :
    (retainedDrawingEightOccurrenceSplitFormula source).IsOneDimensional := by
  apply PeriodicEightOccurrenceSplit.formula_isOneDimensional
  simpa only [retainedPlanarSATFormula] using
    (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula_erase_isOneDimensional
      wellFormed degree isLocal horizontal)

/-- Source-first angular-fan refinement changes the displayed coordinates
but not the horizontal erased fixed-eight formula. -/
theorem
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula_erase_isOneDimensional
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (isLocal : source.incidenceGraph.IsLocal)
    (horizontal : source.incidenceGraph.HasZeroVerticalOffsets) :
    (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
      source).erase.IsOneDimensional := by
  rw [retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula_erase]
  exact retainedDrawingEightOccurrenceSplitFormula_isOneDimensional
    wellFormed degree isLocal horizontal

/-- The first stable clockwise clause ordering preserves the horizontal
fixed-eight source. -/
theorem
    retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula_erase_isOneDimensional
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (isLocal : source.incidenceGraph.IsLocal)
    (horizontal : source.incidenceGraph.HasZeroVerticalOffsets) :
    (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula
      source).erase.IsOneDimensional := by
  apply PositionedPeriodicCNF.orderClausesByRouteDirection_erase_isOneDimensional
  exact
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula_erase_isOneDimensional
      wellFormed degree isLocal horizontal

/-- The whole-source Figure 9 clearance scale leaves the horizontal erased
formula unchanged. -/
theorem retainedFigureNineClearancePositionedFormula_erase_isOneDimensional
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (isLocal : source.incidenceGraph.IsLocal)
    (horizontal : source.incidenceGraph.HasZeroVerticalOffsets) :
    (retainedFigureNineClearancePositionedFormula
      source).erase.IsOneDimensional := by
  simpa only [retainedFigureNineClearancePositionedFormula,
    PositionedPeriodicCNF.erase_scale] using
    (retainedDrawingSourceScaledClockwiseEightOccurrenceSplitPositionedFormula_erase_isOneDimensional
      wellFormed degree isLocal horizontal)

end PeriodicOrthocrossing
end LeanTrominoes
