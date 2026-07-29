import LeanTrominoes.PeriodicCNFPlanarRetainedFixedEightOneInThreePositioned
import LeanTrominoes.PeriodicOneInThreePositionedInheritedRouteFamily

/-!
# Figure 9 routes over retained fixed-eight planar SAT

The generic inherited-route adapter carries each retained angular-spliced
fixed-eight route into its corresponding Figure 9 gadget and completes all
fresh local incidences.  The resulting raw exact-one route family has exact
canonical endpoints and is orthogonal.  Global noncrossing remains dependent
on the retained split's copied-source boundary prefixes.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

set_option maxHeartbeats 800000

/-- Pointwise canonical endpoints of the retained angular-spliced
fixed-eight source routes. -/
theorem
    retainedDrawingEightOccurrenceSplitAngularSplicedIncidenceRoutes_endpoints
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    {clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedDrawingEightOccurrenceSplitPositionedFormula
          source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    (retainedDrawingEightOccurrenceSplitAngularSplicedIncidenceRoutes
        source clauseIndex literalIndex).head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            (retainedDrawingEightOccurrenceSplitPlacement source)
            clause) ∧
      (retainedDrawingEightOccurrenceSplitAngularSplicedIncidenceRoutes
        source clauseIndex literalIndex).getLast? =
        some
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (retainedDrawingEightOccurrenceSplitPlacement source)
            clause literal) := by
  simpa
    [retainedDrawingEightOccurrenceSplitAngularSplicedIncidenceRoutes,
      PeriodicEightOccurrenceSplitPositioned.canonicalAngularSplicedIncidenceRoutes,
      retainedDrawingEightOccurrenceSplitPositionedFormula,
      retainedDrawingEightOccurrenceSplitPlacement] using
    PeriodicEightOccurrenceSplitPositioned.angularSplicedIncidenceRoutes_endpoints
      (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        source)
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement source)
      (retainedDrawingAngularOccurrenceOrder source)
      (PeriodicEightOccurrenceSplitPositioned.canonicalAngularBoundaryRoutes
        (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          source)
        (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement source)
        (retainedDrawingAngularOccurrenceOrder source))
      clauseMember literalMember

/-- Pointwise orthogonality of the retained angular-spliced fixed-eight
source routes. -/
theorem
    retainedDrawingEightOccurrenceSplitAngularSplicedIncidenceRoutes_orthogonal
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    {clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedDrawingEightOccurrenceSplitPositionedFormula
          source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (retainedDrawingEightOccurrenceSplitAngularSplicedIncidenceRoutes
        source clauseIndex literalIndex) := by
  simpa
    [retainedDrawingEightOccurrenceSplitAngularSplicedIncidenceRoutes,
      PeriodicEightOccurrenceSplitPositioned.canonicalAngularSplicedIncidenceRoutes,
      retainedDrawingEightOccurrenceSplitPositionedFormula] using
    PeriodicEightOccurrenceSplitPositioned.angularSplicedIncidenceRoutes_orthogonal
      (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
        source)
      (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement source)
      (retainedDrawingAngularOccurrenceOrder source)
      (PeriodicEightOccurrenceSplitPositioned.canonicalAngularBoundaryRoutes
        (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          source)
        (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement source)
        (retainedDrawingAngularOccurrenceOrder source))
      clauseMember literalMember

/-- Complete inherited Figure 9 suffixes obtained from the retained
fixed-eight source routes. -/
noncomputable def
    retainedFixedEightPeriodicPlanarOneInThreeInheritedRouteSuffixes
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PositionedPeriodicCNF.InheritedCanonicalIncidenceRouteSuffixes
      (PeriodicOneInThreePositioned.formula
        (retainedDrawingEightOccurrenceSplitPositionedFormula source))
      (PeriodicOneInThreePositioned.placement
        (retainedDrawingEightOccurrenceSplitPositionedFormula source)
        (retainedDrawingEightOccurrenceSplitPlacement source))
      (PeriodicOneInThreePositioned.normalizedLocalEndpoint
        (retainedDrawingEightOccurrenceSplitPositionedFormula source)
        (retainedDrawingEightOccurrenceSplitPlacement source)) :=
  PeriodicOneInThreePositioned.inheritedRouteSuffixes
    (retainedDrawingEightOccurrenceSplitPositionedFormula source)
    (retainedDrawingEightOccurrenceSplitPlacement source)
    (retainedDrawingEightOccurrenceSplitPositionedFormula_widthAtMostThree
      source sourceWidth)
    (retainedDrawingEightOccurrenceSplitPositionedFormula_allAtomsNodup
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty)
    (retainedDrawingEightOccurrenceSplitAngularSplicedIncidenceRoutes source)
    (fun _sourceClause _sourceClauseIndex sourceClauseMember
        _sourceLiteral _sourceLiteralIndex sourceLiteralMember =>
      retainedDrawingEightOccurrenceSplitAngularSplicedIncidenceRoutes_endpoints
        source sourceClauseMember sourceLiteralMember)
    (fun _sourceClause _sourceClauseIndex sourceClauseMember
        _sourceLiteral _sourceLiteralIndex sourceLiteralMember =>
      retainedDrawingEightOccurrenceSplitAngularSplicedIncidenceRoutes_orthogonal
        source sourceClauseMember sourceLiteralMember)

/-- Complete local-plus-inherited routes for the raw retained exact-one
formula. -/
noncomputable def
    retainedFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  PeriodicOneInThreePositioned.splicedRoutes
    (retainedDrawingEightOccurrenceSplitPositionedFormula source)
    (retainedDrawingEightOccurrenceSplitPlacement source)
    (retainedFixedEightPeriodicPlanarOneInThreeInheritedRouteSuffixes
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty)

/-- Every genuine raw retained Figure 9 route has exact canonical endpoints
and is orthogonal. -/
theorem
    retainedFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes_valid
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedFixedEightPositionedPeriodicPlanarOneInThreeRawFormula
          source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    (retainedFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseIndex literalIndex).head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            (retainedFixedEightPeriodicPlanarOneInThreeRawPlacement source)
            clause) ∧
      (retainedFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseIndex literalIndex).getLast? =
        some
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (retainedFixedEightPeriodicPlanarOneInThreeRawPlacement source)
            clause literal) ∧
      PeriodicOrthocrossing.OrthogonalPolyline
        (retainedFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty clauseIndex literalIndex) := by
  simpa
    [retainedFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes,
      retainedFixedEightPositionedPeriodicPlanarOneInThreeRawFormula,
      retainedFixedEightPeriodicPlanarOneInThreeRawPlacement] using
    PeriodicOneInThreePositioned.splicedRoutes_valid_of_members
      (retainedDrawingEightOccurrenceSplitPositionedFormula source)
      (retainedDrawingEightOccurrenceSplitPlacement source)
      (retainedDrawingEightOccurrenceSplitPositionedFormula_widthAtMostThree
        source sourceWidth)
      (retainedDrawingEightOccurrenceSplitPositionedFormula_allAtomsNodup
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (retainedFixedEightPeriodicPlanarOneInThreeInheritedRouteSuffixes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      clauseMember literalMember

/-- Every genuine raw retained Figure 9 route records a first exit after its
generated clause endpoint. -/
theorem
    retainedFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes_exists_tail_head?
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedFixedEightPositionedPeriodicPlanarOneInThreeRawFormula
          source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    ∃ exit,
      (retainedFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseIndex literalIndex).tail.head? =
        some exit := by
  simpa
    [retainedFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes,
      retainedFixedEightPositionedPeriodicPlanarOneInThreeRawFormula,
      retainedFixedEightPeriodicPlanarOneInThreeRawPlacement] using
    PeriodicOneInThreePositioned.splicedRoutes_exists_tail_head?_of_members
      (retainedDrawingEightOccurrenceSplitPositionedFormula source)
      (retainedDrawingEightOccurrenceSplitPlacement source)
      (retainedDrawingEightOccurrenceSplitPositionedFormula_widthAtMostThree
        source sourceWidth)
      (retainedDrawingEightOccurrenceSplitPositionedFormula_allAtomsNodup
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      (retainedFixedEightPeriodicPlanarOneInThreeInheritedRouteSuffixes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty)
      clauseMember literalMember

end PeriodicOrthocrossing
end LeanTrominoes
