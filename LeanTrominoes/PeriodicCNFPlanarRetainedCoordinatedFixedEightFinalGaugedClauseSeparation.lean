import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalClauseOrbitSeparation
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalGaugedDrawing

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
private theorem exists_composedRawClause_of_finalGaugedClause_mem
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
  change
    (finalClause, clauseIndex) ∈
      ((retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormula
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty).clauses.map fun clause =>
        ⟨clause.position,
          clause.literals.variableGauge
            (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauge
              source)⟩).zipIdx at finalMember
  rw [List.zipIdx_map] at finalMember
  rcases List.mem_map.mp finalMember with
    ⟨taggedClause, taggedClauseMember, finalClauseEq⟩
  have clauseIndexEq : taggedClause.2 = clauseIndex :=
    congrArg Prod.snd finalClauseEq
  have finalClauseValueEq :
      finalClause =
        ⟨taggedClause.1.position,
          taggedClause.1.literals.variableGauge
            (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauge
              source)⟩ :=
    (congrArg Prod.fst finalClauseEq).symm
  subst clauseIndex
  subst finalClause
  rcases PositionedPeriodicCNF.exists_sourceClause_of_orderedClause_mem
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawNormalizedIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences sourceClausesNonempty)
      taggedClauseMember with
    ⟨rawClause, rawClauseMember, orderedClauseEq⟩
  refine ⟨rawClause, rawClauseMember, ?_⟩
  rw [orderedClauseEq]
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
    rcases firstClause.position with ⟨firstX, firstY⟩
    rcases secondClause.position with ⟨secondX, secondY⟩
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
      Prod.mk.injEq] at positionsEqual ⊢
    constructor <;> nlinarith
  exact
    retainedOrderedFixedEightComposedRawClausePosition_eq_translated_imp_clauseIndex_eq
      source sourceLocal sourceWidth sourceOccurrences sourceClausesNonempty
      firstRawMember secondRawMember relativeTranslate rawPositionsEqual

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
  rw [List.nodup_iff_injective_getElem]
  intro firstIndex secondIndex positionsEqual
  have firstMember :
      ((retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty).clauses[firstIndex.val], firstIndex.val) ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty).clauses.zipIdx :=
    List.mem_zipIdx'.mpr ⟨by simpa using firstIndex.isLt, rfl⟩
  have secondMember :
      ((retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty).clauses[secondIndex.val], secondIndex.val) ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalGaugedFormula
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty).clauses.zipIdx :=
    List.mem_zipIdx'.mpr ⟨by simpa using secondIndex.isLt, rfl⟩
  apply Fin.ext
  apply
    retainedOrderedFixedEightFinalGaugedCanonicalClausePosition_eq_imp_clauseIndex_eq
      source sourceLocal sourceWidth sourceOccurrences sourceClausesNonempty
      firstMember secondMember
  simpa using positionsEqual

end PeriodicOrthocrossing
end LeanTrominoes
