import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOneInThreeNoUnitsRoutes
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOneInThreeTwoPointRoutes
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOneInThreeMiddleRouteDirections
import LeanTrominoes.PeriodicOneInThreeNoUnitsPositionedInheritedSplicedRouteIsolation

/-!
# Final-endpoint isolation after unit elimination

The coordinated wrapped Figure 9 family has isolated endpoints.  Its only
possible one-segment source routes are vertical, so the unit-elimination
connector theorem applies even when the first exit is already the variable
endpoint.  Consequently every complete final route retains an isolated
variable endpoint after unit subdivision.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

set_option maxHeartbeats 2000000

/-- Every genuine route in the final coordinated unit-free exact-one family
has an isolated variable endpoint after unit subdivision. -/
theorem
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes_lastNotInDropLast
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (WrappedPeriodicVariable
            (PeriodicPlanarOneInThreeThreeRawVariable Variable)))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
          source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (OneInThreeNoUnitVariable
          (WrappedPeriodicVariable
            (PeriodicPlanarOneInThreeThreeRawVariable Variable)))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    AxisDirection.LastNotInDropLast
      (AxisDirection.unitSubdividePolyline
        (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty clauseIndex literalIndex)) := by
  simpa only [
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes,
    retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula,
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement,
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsInheritedRouteSuffixes]
    using
      PeriodicOneInThreeNoUnitsPositioned.splicedRoutes_lastNotInDropLast
        (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeFormula
          source)
        (retainedCoordinatedFixedEightPeriodicPlanarOneInThreePlacement source)
        (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeFormula_widthAtMostThree
          source)
        (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeFormula_allAtomsNodup
          source)
        (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty)
        (fun _sourceClause _sourceClauseIndex sourceClauseMember
            _sourceLiteral _sourceLiteralIndex sourceLiteralMember =>
          let valid :=
            retainedCoordinatedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes_valid
              source sourceLocal sourceWidth sourceOccurrences
              sourceClausesNonempty sourceClauseMember sourceLiteralMember
          ⟨valid.1, valid.2.1⟩)
        (fun _sourceClause _sourceClauseIndex sourceClauseMember
            _sourceLiteral _sourceLiteralIndex sourceLiteralMember =>
          (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes_valid
            source sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty
            sourceClauseMember sourceLiteralMember).2.2)
        (fun _sourceClause _sourceClauseIndex sourceClauseMember
            _sourceLiteral _sourceLiteralIndex sourceLiteralMember =>
          retainedCoordinatedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes_exists_tail_head?
            source sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty sourceClauseMember sourceLiteralMember)
        (fun _sourceClause _sourceClauseIndex sourceClauseMember
            _sourceLiteral _sourceLiteralIndex sourceLiteralMember =>
          retainedCoordinatedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes_endpointIsolation
            source sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty sourceClauseMember sourceLiteralMember)
        (fun _sourceClause _sourceClauseIndex sourceClauseMember
            _sourceLiteral _sourceLiteralIndex sourceLiteralMember exit
            routeExit finalIsExit =>
          retainedCoordinatedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes_verticalIfLastIsExit
            source sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty sourceClauseMember sourceLiteralMember
            exit routeExit finalIsExit)
        clauseMember literalMember

/-- Every genuine final unit-free exact-one route contains at least one
edge, inherited from its nondegenerate local unit-elimination prefix. -/
theorem
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes_length_ge_two
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (WrappedPeriodicVariable
            (PeriodicPlanarOneInThreeThreeRawVariable Variable)))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
          source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (OneInThreeNoUnitVariable
          (WrappedPeriodicVariable
            (PeriodicPlanarOneInThreeThreeRawVariable Variable)))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    2 ≤
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseIndex literalIndex).length := by
  simpa only [
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes,
    retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula,
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement]
    using
      PeriodicOneInThreeNoUnitsPositioned.splicedRoutes_length_ge_two_of_members
        (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeFormula
          source)
        (retainedCoordinatedFixedEightPeriodicPlanarOneInThreePlacement source)
        (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeFormula_widthAtMostThree
          source)
        (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeFormula_allAtomsNodup
          source)
        (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsInheritedRouteSuffixes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty)
        clauseMember literalMember

/-- Every genuine route in the final coordinated unit-free exact-one family
has both endpoints isolated after unit subdivision. -/
theorem
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes_endpointIsolation
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (WrappedPeriodicVariable
            (PeriodicPlanarOneInThreeThreeRawVariable Variable)))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
          source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (OneInThreeNoUnitVariable
          (WrappedPeriodicVariable
            (PeriodicPlanarOneInThreeThreeRawVariable Variable)))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    AxisDirection.HeadNotInTail
        (AxisDirection.unitSubdividePolyline
          (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes
            source sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty clauseIndex literalIndex)) ∧
      AxisDirection.LastNotInDropLast
        (AxisDirection.unitSubdividePolyline
          (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes
            source sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty clauseIndex literalIndex)) := by
  simpa only [
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsIncidenceRoutes,
    retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula,
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement,
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsInheritedRouteSuffixes]
    using
      PeriodicOneInThreeNoUnitsPositioned.splicedRoutes_endpointIsolation
        (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeFormula
          source)
        (retainedCoordinatedFixedEightPeriodicPlanarOneInThreePlacement source)
        (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeFormula_widthAtMostThree
          source)
        (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeFormula_allAtomsNodup
          source)
        (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty)
        (fun _sourceClause _sourceClauseIndex sourceClauseMember
            _sourceLiteral _sourceLiteralIndex sourceLiteralMember =>
          let valid :=
            retainedCoordinatedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes_valid
              source sourceLocal sourceWidth sourceOccurrences
              sourceClausesNonempty sourceClauseMember sourceLiteralMember
          ⟨valid.1, valid.2.1⟩)
        (fun _sourceClause _sourceClauseIndex sourceClauseMember
            _sourceLiteral _sourceLiteralIndex sourceLiteralMember =>
          (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes_valid
            source sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty
            sourceClauseMember sourceLiteralMember).2.2)
        (fun _sourceClause _sourceClauseIndex sourceClauseMember
            _sourceLiteral _sourceLiteralIndex sourceLiteralMember =>
          retainedCoordinatedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes_exists_tail_head?
            source sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty sourceClauseMember sourceLiteralMember)
        (fun _sourceClause _sourceClauseIndex sourceClauseMember
            _sourceLiteral _sourceLiteralIndex sourceLiteralMember =>
          retainedCoordinatedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes_endpointIsolation
            source sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty sourceClauseMember sourceLiteralMember)
        (fun _sourceClause _sourceClauseIndex sourceClauseMember
            _sourceLiteral _sourceLiteralIndex sourceLiteralMember exit
            routeExit finalIsExit =>
          retainedCoordinatedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes_verticalIfLastIsExit
            source sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty sourceClauseMember sourceLiteralMember
            exit routeExit finalIsExit)
        (fun _sourceClause _sourceClauseIndex sourceClauseMember
            _sourceLiteral sourceLiteralMember exit routeExit =>
          retainedCoordinatedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes_middle_doesNotExitRight
            source sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty sourceClauseMember sourceLiteralMember
            exit routeExit)
        clauseMember literalMember

end PeriodicOrthocrossing
end LeanTrominoes
