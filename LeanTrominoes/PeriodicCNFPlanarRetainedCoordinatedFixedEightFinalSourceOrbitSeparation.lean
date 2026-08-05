import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalVariableOrbits
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOrderedFigureNineLocalRouteSeparation

/-!
# Orbit separation of the final Figure Nine source macrocells

The last two gadget layers refine the retained clockwise fixed-eight source.
This file records that genuine source clauses and source variables remain
injective even modulo a whole source period.  These are the global inputs to
the finite `72 × 72` local-code collision argument.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicThreeSATThree

/-- Stored clearance-clause positions identify their presentation indices
even modulo a whole clearance period.  Subtracting each clause anchor turns
the asserted stored-position equality into the existing canonical-position
separation statement. -/
theorem retainedFigureNineClearanceClausePosition_eq_translated_imp_clauseIndex_eq
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {firstClause secondClause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {firstClauseIndex secondClauseIndex : Nat}
    (firstMember :
      (firstClause, firstClauseIndex) ∈
        (retainedFigureNineClearancePositionedFormula source).clauses.zipIdx)
    (secondMember :
      (secondClause, secondClauseIndex) ∈
        (retainedFigureNineClearancePositionedFormula source).clauses.zipIdx)
    (relativeTranslate : Cell)
    (positionsEqual :
      firstClause.position =
        Cell.add
          ((retainedFigureNineClearancePlacement source).translation
            relativeTranslate)
          secondClause.position) :
    firstClauseIndex = secondClauseIndex := by
  rcases exists_clockwiseClause_of_clearanceClause_mem firstMember with
    ⟨firstSourceClause, firstSourceMember, firstClauseEqual⟩
  rcases exists_clockwiseClause_of_clearanceClause_mem secondMember with
    ⟨secondSourceClause, secondSourceMember, secondClauseEqual⟩
  subst firstClause
  subst secondClause
  let placement :=
    retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement source
  have unscaledPositionsEqual :
      firstSourceClause.position =
        Cell.add (placement.translation relativeTranslate)
          secondSourceClause.position := by
    apply Cell.scale_injective
      (show (retainedFigureNineSourceClearanceFactor : Int) ≠ 0 by
        simp [retainedFigureNineSourceClearanceFactor])
    simpa [placement, retainedFigureNineClearancePlacement,
      Cell.scale_add] using positionsEqual
  let adjustedTranslate :=
    Cell.add
      (Cell.sub relativeTranslate
        (PeriodicCNF.clauseAnchor firstSourceClause.literals))
      (PeriodicCNF.clauseAnchor secondSourceClause.literals)
  have canonicalPositionsEqual :
      PositionedPeriodicCNF.canonicalClausePosition
          placement firstSourceClause =
        Cell.add (placement.translation adjustedTranslate)
          (PositionedPeriodicCNF.canonicalClausePosition
            placement secondSourceClause) := by
    rcases firstPositionEq : firstSourceClause.position with
      ⟨firstX, firstY⟩
    rcases secondPositionEq : secondSourceClause.position with
      ⟨secondX, secondY⟩
    rcases firstAnchorEq :
        PeriodicCNF.clauseAnchor firstSourceClause.literals with
      ⟨firstAnchorX, firstAnchorY⟩
    rcases secondAnchorEq :
        PeriodicCNF.clauseAnchor secondSourceClause.literals with
      ⟨secondAnchorX, secondAnchorY⟩
    rcases relativeTranslate with ⟨translateX, translateY⟩
    simp only [PositionedPeriodicCNF.canonicalClausePosition,
      adjustedTranslate, PeriodicVariablePlacement.translation,
      Cell.add, Cell.sub, Cell.scale, firstPositionEq,
      secondPositionEq, firstAnchorEq, secondAnchorEq,
      Prod.mk.injEq] at unscaledPositionsEqual ⊢
    constructor <;> nlinarith
  exact
    retainedOrderedFixedEightCanonicalClausePosition_eq_translated_imp_clauseIndex_eq
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty firstSourceMember secondSourceMember
      adjustedTranslate canonicalPositionsEqual

/-- Consequently two genuine clearance clauses in the same stored-position
orbit are the same positioned clause as well as the same list entry. -/
theorem retainedFigureNineClearanceClausePosition_eq_translated_imp_eq
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {firstClause secondClause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {firstClauseIndex secondClauseIndex : Nat}
    (firstMember :
      (firstClause, firstClauseIndex) ∈
        (retainedFigureNineClearancePositionedFormula source).clauses.zipIdx)
    (secondMember :
      (secondClause, secondClauseIndex) ∈
        (retainedFigureNineClearancePositionedFormula source).clauses.zipIdx)
    (relativeTranslate : Cell)
    (positionsEqual :
      firstClause.position =
        Cell.add
          ((retainedFigureNineClearancePlacement source).translation
            relativeTranslate)
          secondClause.position) :
    firstClause = secondClause := by
  have indicesEqual :=
    retainedFigureNineClearanceClausePosition_eq_translated_imp_clauseIndex_eq
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty firstMember secondMember
      relativeTranslate positionsEqual
  subst secondClauseIndex
  have firstLookup := (List.mem_zipIdx_iff_getElem?).mp firstMember
  have secondLookup := (List.mem_zipIdx_iff_getElem?).mp secondMember
  rw [firstLookup] at secondLookup
  exact Option.some.inj (by simpa using secondLookup)

end PeriodicOrthocrossing
end LeanTrominoes
