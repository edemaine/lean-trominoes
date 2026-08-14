/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarHorizontalRetainedFixedEight
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalClauseOrdering
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineSemantics
import LeanTrominoes.PeriodicOneInThreeNoUnitsOneDimensional
import LeanTrominoes.PeriodicOneInThreeOneDimensional

/-!
# One-dimensional retained exact-one endpoint

The concrete retained fixed-eight source remains one-dimensional through the
Figure 9 exact-one construction, unit-clause elimination, and the final
stable clause-direction ordering.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- The concrete twice-replaced unit-free exact-one endpoint is horizontal
before its final stable clause ordering. -/
theorem
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula_erase_isOneDimensional
    {Variable : Type*} [DecidableEq Variable]
    {source : PeriodicCNF Variable}
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (graphLocal : source.incidenceGraph.IsLocal)
    (horizontal : source.incidenceGraph.HasZeroVerticalOffsets) :
    (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
      source).erase.IsOneDimensional := by
  rw [
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula_erase]
  apply PeriodicOneInThreeNoUnits.formula_isOneDimensional
  apply PeriodicOneInThree.formula_isOneDimensional
  exact retainedFigureNineClearancePositionedFormula_erase_isOneDimensional
    wellFormed degree graphLocal horizontal

/-- The final stable clockwise clause ordering preserves the horizontal
unit-free exact-one endpoint. -/
theorem
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormula_erase_isOneDimensional
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
    (horizontal : source.incidenceGraph.HasZeroVerticalOffsets) :
    ((retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormula
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).erase).IsOneDimensional := by
  apply PositionedPeriodicCNF.orderClausesByRouteDirection_erase_isOneDimensional
  exact
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula_erase_isOneDimensional
      wellFormed degree graphLocal horizontal

end PeriodicOrthocrossing
end LeanTrominoes
