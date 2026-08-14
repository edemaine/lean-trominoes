/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarHorizontalRetainedFinalGaugeOccurrenceProvenance

/-!
# Occurring variables have a horizontal final gauge

The inherited/local provenance dichotomy applies the corresponding endpoint
bound to every variable occurring before the final gauge.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- The final canonical position gauge is vertically zero on every variable
occurring before the gauge is applied. -/
theorem
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauge_vertical_eq_zero_of_mem
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
    (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauge
      source atom).2 = 0 := by
  rcases
      finalClockwise_mem_inherited_or_exists_horizontal_local_occurrence
        wellFormed degree graphLocal sourceLocal sourceWidth
        sourceOccurrences sourceClausesNonempty horizontal atomMember with
    ⟨sourceAtom, rfl, sourceAtomMember⟩ |
      ⟨rawClause, rawClauseIndex, rawLiteral, rawLiteralIndex,
        rfl, rawClauseMember, rawLiteralMember, rawLiteralVertical,
        notInherited⟩
  · exact
      retainedOrderedFixedEightFinalGauge_vertical_eq_zero_of_inherited
        source sourceAtom sourceAtomMember
  · exact
      retainedOrderedFixedEightFinalGauge_vertical_eq_zero_of_local_literal
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty rawClauseMember rawLiteralMember
        rawLiteralVertical notInherited

end PeriodicOrthocrossing
end LeanTrominoes
