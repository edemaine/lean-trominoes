/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalClauseOrbitSeparation
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalGaugedDrawing
import LeanTrominoes.PositionedPeriodicCNFVariableGaugeClauseMembership

/-!
# Clause separation in the final canonical gauge

The final literal ordering and variable gauge preserve clause presentation
indices and stored clause positions.  Equality of canonical clause vertices
therefore gives equality of the underlying raw stored positions modulo a
whole final period, where raw orbit separation applies.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

set_option maxHeartbeats 2000000

local instance finalGaugedClauseSeparationDecidableEq
    {Variable : Type*} [DecidableEq Variable] :
    DecidableEq
      (OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :=
  PlanarOneInThreeNoUnitsFigureNine.nestedVariableDecidableEq

/-- A genuine clause of the final gauged presentation recovers the raw
composed clause at exactly the same presentation index and stored position. -/
theorem exists_composedRawClause_of_finalGaugedClause_mem
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {finalClause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {clauseIndex : Nat}
    (finalMember :
      (finalClause, clauseIndex) ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty).clauses.zipIdx) :
    ∃ rawClause,
      (rawClause, clauseIndex) ∈
          (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
            source).clauses.zipIdx ∧
        finalClause.position = rawClause.position := by
  have finalMember' :
      (finalClause, clauseIndex) ∈
        ((retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormula
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty).variableGauge
            (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauge
              source)).clauses.zipIdx := by
    simpa only [
      retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula]
      using finalMember
  rcases PositionedPeriodicCNF.exists_sourceClause_of_variableGaugeClause_mem
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormula
        source sourceLocal sourceWidth sourceOccurrences sourceClausesNonempty)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauge source)
      finalMember' with
    ⟨orderedClause, orderedClauseMember, finalClauseEq⟩
  rcases PositionedPeriodicCNF.exists_sourceClause_of_orderedClause_mem
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences sourceClausesNonempty)
      orderedClauseMember with
    ⟨rawClause, rawClauseMember, orderedClauseEq⟩
  refine ⟨rawClause, rawClauseMember, ?_⟩
  rw [finalClauseEq, orderedClauseEq]
  rfl

/-- Canonical final clause positions identify their unchanged presentation
indices. -/
theorem retainedOrderedFixedEightFinalGaugedCanonicalClausePosition_eq_imp_clauseIndex_eq
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {firstClause secondClause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {firstClauseIndex secondClauseIndex : Nat}
    (firstMember :
      (firstClause, firstClauseIndex) ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty).clauses.zipIdx)
    (secondMember :
      (secondClause, secondClauseIndex) ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty).clauses.zipIdx)
    (positionsEqual :
      PositionedPeriodicCNF.canonicalClausePosition
          (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
            source) firstClause =
        PositionedPeriodicCNF.canonicalClausePosition
          (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
            source) secondClause) :
    firstClauseIndex = secondClauseIndex := by
  rcases exists_composedRawClause_of_finalGaugedClause_mem
      source sourceLocal sourceWidth sourceOccurrences sourceClausesNonempty
      firstMember with
    ⟨firstRawClause, firstRawMember, firstStoredPosition⟩
  rcases exists_composedRawClause_of_finalGaugedClause_mem
      source sourceLocal sourceWidth sourceOccurrences sourceClausesNonempty
      secondMember with
    ⟨secondRawClause, secondRawMember, secondStoredPosition⟩
  let relativeTranslate :=
    Cell.sub
      (PeriodicCNF.clauseAnchor firstClause.literals)
      (PeriodicCNF.clauseAnchor secondClause.literals)
  have rawPositionsEqual :
      firstRawClause.position =
        Cell.add
          ((retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
              source).translation relativeTranslate)
          secondRawClause.position := by
    rw [← firstStoredPosition, ← secondStoredPosition]
    rcases firstPositionEq : firstClause.position with ⟨firstX, firstY⟩
    rcases secondPositionEq : secondClause.position with ⟨secondX, secondY⟩
    rcases firstAnchorEq :
        PeriodicCNF.clauseAnchor firstClause.literals with
      ⟨firstAnchorX, firstAnchorY⟩
    rcases secondAnchorEq :
        PeriodicCNF.clauseAnchor secondClause.literals with
      ⟨secondAnchorX, secondAnchorY⟩
    simp only [PositionedPeriodicCNF.canonicalClausePosition,
      retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement,
      PeriodicVariablePlacement.variableGauge_period,
      PeriodicVariablePlacement.translation, Cell.add, Cell.sub, Cell.scale,
      relativeTranslate, firstAnchorEq, secondAnchorEq,
      firstPositionEq, secondPositionEq, Prod.mk.injEq]
      at positionsEqual ⊢
    constructor
    · linear_combination positionsEqual.1
    · linear_combination positionsEqual.2
  exact
    retainedOrderedFixedEightComposedRawClausePosition_eq_translated_imp_clauseIndex_eq
      source sourceLocal sourceWidth sourceOccurrences sourceClausesNonempty
      firstRawMember secondRawMember relativeTranslate rawPositionsEqual

private theorem canonicalClausePositions_nodup_of_index_injective
    {Variable : Type*}
    (formula : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (indexInjective :
      ∀ {firstClause secondClause : PositionedPeriodicClause Variable}
          {firstClauseIndex secondClauseIndex : Nat},
        (firstClause, firstClauseIndex) ∈ formula.clauses.zipIdx →
        (secondClause, secondClauseIndex) ∈ formula.clauses.zipIdx →
        PositionedPeriodicCNF.canonicalClausePosition placement firstClause =
          PositionedPeriodicCNF.canonicalClausePosition placement secondClause →
        firstClauseIndex = secondClauseIndex) :
    (formula.clauses.map
      (PositionedPeriodicCNF.canonicalClausePosition placement)).Nodup := by
  rw [List.nodup_iff_injective_getElem]
  intro firstIndex secondIndex positionsEqual
  apply Fin.ext
  apply indexInjective
  · apply List.mk_mem_zipIdx_iff_getElem?.mpr
    exact List.getElem?_eq_getElem (by simpa using firstIndex.isLt)
  · apply List.mk_mem_zipIdx_iff_getElem?.mpr
    exact List.getElem?_eq_getElem (by simpa using secondIndex.isLt)
  · simpa using positionsEqual

/-- The canonical clause-position suffix of the final incidence drawing has
no collisions. -/
theorem retainedOrderedFixedEightFinalGaugedCanonicalClausePositions_nodup
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    ((retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty).clauses.map
      (PositionedPeriodicCNF.canonicalClausePosition
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedPlacement
          source))).Nodup := by
  apply canonicalClausePositions_nodup_of_index_injective
  intro firstClause secondClause firstClauseIndex secondClauseIndex
    firstMember secondMember positionsEqual
  exact
    retainedOrderedFixedEightFinalGaugedCanonicalClausePosition_eq_imp_clauseIndex_eq
      source sourceLocal sourceWidth sourceOccurrences sourceClausesNonempty
      firstMember secondMember positionsEqual

end PeriodicOrthocrossing
end LeanTrominoes
