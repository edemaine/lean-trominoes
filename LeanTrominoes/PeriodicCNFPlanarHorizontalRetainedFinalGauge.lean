/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFOneDimensionalGauge
import LeanTrominoes.PeriodicCNFPlanarHorizontalRetainedFinalGaugeOccurrences

/-!
# One-dimensional final retained canonical gauge

The occurrence-wise vertical gauge bound supplies the final premise of the
generic one-dimensional variable-gauge theorem.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- Applying the final canonical variable gauge preserves the concrete
retained exact-one endpoint's one-dimensionality. -/
theorem
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula_erase_isOneDimensional
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
    (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).erase.IsOneDimensional := by
  rw [
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula,
    PositionedPeriodicCNF.erase_variableGauge]
  apply PeriodicCNF.variableGauge_isOneDimensional
  · exact
      retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormula_erase_isOneDimensional
        wellFormed degree graphLocal sourceLocal sourceWidth
        sourceOccurrences sourceClausesNonempty horizontal
  · intro atom atomMember
    exact
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauge_vertical_eq_zero_of_mem
        wellFormed degree graphLocal sourceLocal sourceWidth
        sourceOccurrences sourceClausesNonempty horizontal atomMember

end PeriodicOrthocrossing
end LeanTrominoes
