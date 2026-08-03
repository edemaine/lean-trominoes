import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOneInThreeWrappedRoutes
import LeanTrominoes.PeriodicOneInThreePositionedTwoPointRoutes

/-!
# Two-point routes in the concrete coordinated Figure 9 drawing

The generic Figure 9 two-point invariant is instantiated on the retained
coordinated fixed-eight source and then transported through opaque wrapping.
It supplies the exceptional vertical-segment fact needed by unit elimination.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

set_option maxHeartbeats 2000000

/-- Every two-point route in the raw coordinated Figure 9 drawing is
vertical. -/
theorem
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes_twoPoint_vertical
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty : ∀ clause ∈ source.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeRawFormula
          source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    {head exit : Cell}
    (routePair :
      retainedCoordinatedFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseIndex literalIndex = [head, exit]) :
    exit.1 = head.1 := by
  simpa only [
    retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeRawFormula,
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes,
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeInheritedRouteSuffixes]
    using
      PeriodicOneInThreePositioned.inheritedSplicedRoutes_twoPoint_vertical
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
          source)
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement source)
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula_widthAtMostThree
          source sourceWidth)
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula_allAtomsNodup
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty)
        (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
          source)
        (fun _sourceClause _sourceClauseIndex sourceClauseMember
            _sourceLiteral _sourceLiteralIndex sourceLiteralMember =>
          let valid :=
            retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_valid
              source sourceLocal sourceWidth sourceOccurrences
              sourceClausesNonempty sourceClauseMember sourceLiteralMember
          ⟨valid.1, valid.2.1⟩)
        (fun _sourceClause _sourceClauseIndex sourceClauseMember
            _sourceLiteral _sourceLiteralIndex sourceLiteralMember =>
          (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_valid
            source sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty sourceClauseMember sourceLiteralMember).2.2)
        clauseMember literalMember routePair

/-- Opaque wrapping preserves the raw drawing's two-point verticality. -/
theorem
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes_twoPoint_vertical
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty : ∀ clause ∈ source.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeFormula
          source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (WrappedPeriodicVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    {head exit : Cell}
    (routePair :
      retainedCoordinatedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseIndex literalIndex = [head, exit]) :
    exit.1 = head.1 := by
  let rawFormula :=
    retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeRawFormula
      source
  let routes :=
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  have transferred :=
    PositionedPeriodicCNF.incidenceIndexProperty_rename
      rawFormula WrappedPeriodicVariable.mk
      (fun sourceClauseIndex sourceLiteralIndex =>
        ∀ head exit,
          routes sourceClauseIndex sourceLiteralIndex = [head, exit] →
          exit.1 = head.1)
      (fun _sourceClause _sourceClauseIndex sourceClauseMember
          _sourceLiteral _sourceLiteralIndex sourceLiteralMember =>
        fun head exit routePair =>
          retainedCoordinatedFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes_twoPoint_vertical
            source sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty sourceClauseMember sourceLiteralMember
            routePair)
      clauseMember literalMember
  simpa [
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes,
    retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeFormula,
    rawFormula, routes] using transferred head exit routePair

/-- If a wrapped coordinated Figure 9 route ends at its first exit, that
route's one segment is vertical. -/
theorem
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes_verticalIfLastIsExit
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty : ∀ clause ∈ source.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeFormula
          source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (WrappedPeriodicVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (exit : Cell)
    (routeExit :
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseIndex literalIndex).tail.head? =
          some exit)
    (finalIsExit :
      PositionedPeriodicCNF.canonicalLiteralPosition
        (retainedCoordinatedFixedEightPeriodicPlanarOneInThreePlacement source)
        clause literal = exit) :
    exit.1 =
      (PositionedPeriodicCNF.canonicalClausePosition
        (retainedCoordinatedFixedEightPeriodicPlanarOneInThreePlacement source)
        clause).1 := by
  have valid :=
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes_valid
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember
  have routeLast :
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseIndex literalIndex).getLast? =
          some exit := by
    rw [valid.2.1, finalIsExit]
  have routePair :=
    PeriodicOneInThreeNoUnitsPositioned.eq_pair_of_last_eq_firstExit
      valid.1 routeExit routeLast valid.2.2
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes_endpointIsolation
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember).2
  exact
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes_twoPoint_vertical
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember routePair

end PeriodicOrthocrossing
end LeanTrominoes
