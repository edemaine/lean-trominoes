import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOneInThreeWrappedRoutes
import LeanTrominoes.PeriodicOneInThreePositionedMiddleRouteDirections

/-!
# Middle-route exits in the coordinated Figure 9 family

The generic weak-left Figure 9 invariant is specialized to the retained
coordinated family and then transported through opaque variable wrapping.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

set_option maxHeartbeats 2000000

/-- Every literal-index-one raw coordinated Figure 9 route first exits
weakly left of its canonical clause point. -/
theorem
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes_middle_doesNotExitRight
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
      PeriodicLiteral (PeriodicPlanarOneInThreeThreeRawVariable Variable)}
    (literalMember : (literal, 1) ∈ clause.literals.zipIdx)
    (exit : Cell)
    (routeExit :
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseIndex 1).tail.head? = some exit) :
    exit.1 ≤
      (PositionedPeriodicCNF.canonicalClausePosition
        (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeRawPlacement
          source)
        clause).1 := by
  simpa only [
    retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeRawFormula,
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeRawPlacement,
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes,
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeInheritedRouteSuffixes]
    using
      PeriodicOneInThreePositioned.splicedRoutes_middle_doesNotExitRight
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
          source)
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPlacement source)
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula_widthAtMostThree
          source sourceWidth)
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula_allAtomsNodup
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty)
        (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeInheritedRouteSuffixes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty)
        clauseMember literalMember exit routeExit

/-- Opaque wrapping preserves the coordinated middle route's weak-left
first exit. -/
theorem
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes_middle_doesNotExitRight
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
    (literalMember : (literal, 1) ∈ clause.literals.zipIdx)
    (exit : Cell)
    (routeExit :
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseIndex 1).tail.head? = some exit) :
    exit.1 ≤
      (PositionedPeriodicCNF.canonicalClausePosition
        (retainedCoordinatedFixedEightPeriodicPlanarOneInThreePlacement source)
        clause).1 := by
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
        sourceLiteralIndex = 1 →
          ∀ head exit,
            (routes sourceClauseIndex sourceLiteralIndex).head? =
                some head →
              (routes sourceClauseIndex sourceLiteralIndex).tail.head? =
                some exit →
              exit.1 ≤ head.1)
      (fun sourceClause sourceClauseIndex sourceClauseMember
          sourceLiteral sourceLiteralIndex sourceLiteralMember
          middleIndex head exit sourceHead sourceExit => by
        subst sourceLiteralIndex
        have weakLeft :=
          retainedCoordinatedFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes_middle_doesNotExitRight
            source sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty sourceClauseMember sourceLiteralMember
            exit sourceExit
        have canonicalHead :=
          (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes_valid
            source sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty sourceClauseMember sourceLiteralMember).1
        have headEqual : head =
            PositionedPeriodicCNF.canonicalClausePosition
              (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeRawPlacement
                source)
              sourceClause :=
          Option.some.inj (sourceHead.symm.trans canonicalHead)
        simpa [headEqual] using weakLeft)
      clauseMember literalMember
  have valid :=
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes_valid
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember
  exact transferred rfl
    (PositionedPeriodicCNF.canonicalClausePosition
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreePlacement source)
      clause)
    exit valid.1 routeExit

end PeriodicOrthocrossing
end LeanTrominoes
