/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarHorizontalRetainedExactOne
import LeanTrominoes.PositionedPeriodicCNFOccurrenceSelection

/-!
# Final clause ordering preserves raw retained occurrences
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- Every atom occurring after the final stable clause sort already occurs
in the unsorted composed Figure 9 formula. -/
theorem finalClockwise_variableOccurrence_mem_composedRaw
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {atom :
      OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)}
    (atomMember :
      atom ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormula
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty).erase.variableOccurrences) :
    atom ∈
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
        source).erase.variableOccurrences := by
  have occurrencePermutation :=
    PositionedPeriodicCNF.orderClausesByRouteDirection_variableOccurrences_perm
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
        source)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
  exact occurrencePermutation.mem_iff.mp
    (by
      simpa only [
        retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormula]
        using atomMember)

/-- Every atom occurring after the final clause sort has an indexed raw
occurrence whose vertical offset is zero. -/
theorem
    exists_horizontal_composedRaw_occurrence_of_finalClockwise_mem
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
    (horizontal : source.incidenceGraph.HasZeroVerticalOffsets)
    {atom :
      OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)}
    (atomMember :
      atom ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormula
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty).erase.variableOccurrences) :
    ∃ rawClause rawClauseIndex rawLiteral rawLiteralIndex,
      (rawClause, rawClauseIndex) ∈
          (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
            source).clauses.zipIdx ∧
        (rawLiteral, rawLiteralIndex) ∈ rawClause.literals.zipIdx ∧
        rawLiteral.atom = atom ∧
        rawLiteral.offset.2 = 0 := by
  let rawFormula :=
    retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
      source
  have rawMember : atom ∈ rawFormula.erase.variableOccurrences := by
    simpa only [rawFormula] using
      (finalClockwise_variableOccurrence_mem_composedRaw
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty atomMember)
  have rawHorizontal : rawFormula.erase.IsOneDimensional := by
    simpa only [rawFormula] using
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula_erase_isOneDimensional
        wellFormed degree graphLocal horizontal)
  exact
    PositionedPeriodicCNF.exists_indexedHorizontalOccurrence_of_mem_variableOccurrences
      rawFormula rawHorizontal rawMember

end PeriodicOrthocrossing
end LeanTrominoes
