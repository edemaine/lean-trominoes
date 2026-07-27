import LeanTrominoes.PeriodicCNFPlanarFixedEightOneInThreePositioned
import LeanTrominoes.PeriodicOneInThreePositionedInheritedRouteFamily

/-!
# Complete Figure 9 routes over the fixed-eight hardness pipeline

This file specializes the generic inherited-route adapter to the concrete
angular-spliced routes of the positioned fixed-eight occurrence split.  It
then invokes the existing Figure 9 local-route splice, completing both
inherited source incidences and fresh auxiliary incidences.

The resulting route family has exact canonical endpoints and is orthogonal.
Its source-port connectors remain generic Manhattan detours, so global
planarity is deliberately not claimed here.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

set_option maxHeartbeats 800000

/-- Pointwise canonical endpoints of the concrete angular-spliced
fixed-eight source routes. -/
theorem
    drawingEightOccurrenceSplitAngularSplicedIncidenceRoutes_endpoints
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable)
    {clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (drawingAngularEightOccurrenceSplitPositionedFormula
          input).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    (drawingEightOccurrenceSplitAngularSplicedIncidenceRoutes
        input clauseIndex literalIndex).head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            (drawingAngularEightOccurrenceSplitPlacement input)
            clause) ∧
      (drawingEightOccurrenceSplitAngularSplicedIncidenceRoutes
        input clauseIndex literalIndex).getLast? =
        some
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (drawingAngularEightOccurrenceSplitPlacement input)
            clause literal) := by
  simpa [drawingEightOccurrenceSplitAngularSplicedIncidenceRoutes,
    PeriodicEightOccurrenceSplitPositioned.canonicalAngularSplicedIncidenceRoutes,
    drawingAngularEightOccurrenceSplitPositionedFormula,
    drawingAngularEightOccurrenceSplitPlacement] using
    PeriodicEightOccurrenceSplitPositioned.angularSplicedIncidenceRoutes_endpoints
      (deduplicatedWrappedDrawingPositionedPeriodicPlanarSATFormula
        input)
      (wrappedDrawingPeriodicPlanarSATPlacement input)
      (drawingOrderedAngularOccurrenceOrder input)
      (PeriodicEightOccurrenceSplitPositioned.canonicalAngularBoundaryRoutes
        (deduplicatedWrappedDrawingPositionedPeriodicPlanarSATFormula
          input)
        (wrappedDrawingPeriodicPlanarSATPlacement input)
        (drawingOrderedAngularOccurrenceOrder input))
      clauseMember literalMember

/-- Pointwise orthogonality of the concrete angular-spliced fixed-eight
source routes. -/
theorem
    drawingEightOccurrenceSplitAngularSplicedIncidenceRoutes_orthogonal
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable)
    {clause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (drawingAngularEightOccurrenceSplitPositionedFormula
          input).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    PeriodicOrthocrossing.OrthogonalPolyline
      (drawingEightOccurrenceSplitAngularSplicedIncidenceRoutes
        input clauseIndex literalIndex) := by
  simpa [drawingEightOccurrenceSplitAngularSplicedIncidenceRoutes,
    PeriodicEightOccurrenceSplitPositioned.canonicalAngularSplicedIncidenceRoutes,
    drawingAngularEightOccurrenceSplitPositionedFormula] using
    PeriodicEightOccurrenceSplitPositioned.angularSplicedIncidenceRoutes_orthogonal
      (deduplicatedWrappedDrawingPositionedPeriodicPlanarSATFormula
        input)
      (wrappedDrawingPeriodicPlanarSATPlacement input)
      (drawingOrderedAngularOccurrenceOrder input)
      (PeriodicEightOccurrenceSplitPositioned.canonicalAngularBoundaryRoutes
        (deduplicatedWrappedDrawingPositionedPeriodicPlanarSATFormula
          input)
        (wrappedDrawingPeriodicPlanarSATPlacement input)
        (drawingOrderedAngularOccurrenceOrder input))
      clauseMember literalMember

/-- Complete inherited Figure 9 suffixes obtained from the concrete
fixed-eight source routes. -/
noncomputable def
    drawingFixedEightPeriodicPlanarOneInThreeInheritedRouteSuffixes
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable)
    (sourceLocal : input.IsLocal)
    (sourceWidth : input.WidthAtMost 3)
    (sourceOccurrences : input.OccurrencesAtMost 3) :
    PositionedPeriodicCNF.InheritedCanonicalIncidenceRouteSuffixes
      (PeriodicOneInThreePositioned.formula
        (drawingAngularEightOccurrenceSplitPositionedFormula input))
      (PeriodicOneInThreePositioned.placement
        (drawingAngularEightOccurrenceSplitPositionedFormula input)
        (drawingAngularEightOccurrenceSplitPlacement input))
      (PeriodicOneInThreePositioned.normalizedLocalEndpoint
        (drawingAngularEightOccurrenceSplitPositionedFormula input)
        (drawingAngularEightOccurrenceSplitPlacement input)) :=
  PeriodicOneInThreePositioned.inheritedRouteSuffixes
    (drawingAngularEightOccurrenceSplitPositionedFormula input)
    (drawingAngularEightOccurrenceSplitPlacement input)
    (drawingAngularEightOccurrenceSplitPositionedFormula_widthAtMostThree
      input sourceWidth)
    (drawingAngularEightOccurrenceSplitPositionedFormula_allAtomsNodup
      input sourceLocal sourceWidth sourceOccurrences)
    (drawingEightOccurrenceSplitAngularSplicedIncidenceRoutes input)
    (fun _sourceClause _sourceClauseIndex sourceClauseMember
        _sourceLiteral _sourceLiteralIndex sourceLiteralMember =>
      drawingEightOccurrenceSplitAngularSplicedIncidenceRoutes_endpoints
        input sourceClauseMember sourceLiteralMember)
    (fun _sourceClause _sourceClauseIndex sourceClauseMember
        _sourceLiteral _sourceLiteralIndex sourceLiteralMember =>
      drawingEightOccurrenceSplitAngularSplicedIncidenceRoutes_orthogonal
        input sourceClauseMember sourceLiteralMember)

/-- Complete local-plus-inherited Figure 9 routes for the raw fixed-eight
exact-one formula. -/
noncomputable def
    drawingFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable)
    (sourceLocal : input.IsLocal)
    (sourceWidth : input.WidthAtMost 3)
    (sourceOccurrences : input.OccurrencesAtMost 3) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  PeriodicOneInThreePositioned.splicedRoutes
    (drawingAngularEightOccurrenceSplitPositionedFormula input)
    (drawingAngularEightOccurrenceSplitPlacement input)
    (drawingFixedEightPeriodicPlanarOneInThreeInheritedRouteSuffixes
      input sourceLocal sourceWidth sourceOccurrences)

/-- Every genuine raw fixed-eight Figure 9 route has exact canonical
endpoints and is orthogonal. -/
theorem
    drawingFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes_valid
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable)
    (sourceLocal : input.IsLocal)
    (sourceWidth : input.WidthAtMost 3)
    (sourceOccurrences : input.OccurrencesAtMost 3)
    {clause :
      PositionedPeriodicClause
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (drawingFixedEightPositionedPeriodicPlanarOneInThreeRawFormula
          input).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    (drawingFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes
        input sourceLocal sourceWidth sourceOccurrences
        clauseIndex literalIndex).head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            (drawingFixedEightPeriodicPlanarOneInThreeRawPlacement input)
            clause) ∧
      (drawingFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes
        input sourceLocal sourceWidth sourceOccurrences
        clauseIndex literalIndex).getLast? =
        some
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (drawingFixedEightPeriodicPlanarOneInThreeRawPlacement input)
            clause literal) ∧
      PeriodicOrthocrossing.OrthogonalPolyline
        (drawingFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes
          input sourceLocal sourceWidth sourceOccurrences
          clauseIndex literalIndex) := by
  simpa
    [drawingFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes,
      drawingFixedEightPositionedPeriodicPlanarOneInThreeRawFormula,
      drawingFixedEightPeriodicPlanarOneInThreeRawPlacement] using
    PeriodicOneInThreePositioned.splicedRoutes_valid_of_members
      (drawingAngularEightOccurrenceSplitPositionedFormula input)
      (drawingAngularEightOccurrenceSplitPlacement input)
      (drawingAngularEightOccurrenceSplitPositionedFormula_widthAtMostThree
        input sourceWidth)
      (drawingAngularEightOccurrenceSplitPositionedFormula_allAtomsNodup
        input sourceLocal sourceWidth sourceOccurrences)
      (drawingFixedEightPeriodicPlanarOneInThreeInheritedRouteSuffixes
        input sourceLocal sourceWidth sourceOccurrences)
      clauseMember literalMember

/-- Every genuine raw fixed-eight Figure 9 route records a first exit after
its generated clause endpoint. -/
theorem
    drawingFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes_exists_tail_head?
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable)
    (sourceLocal : input.IsLocal)
    (sourceWidth : input.WidthAtMost 3)
    (sourceOccurrences : input.OccurrencesAtMost 3)
    {clause :
      PositionedPeriodicClause
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (drawingFixedEightPositionedPeriodicPlanarOneInThreeRawFormula
          input).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    ∃ exit,
      (drawingFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes
        input sourceLocal sourceWidth sourceOccurrences
        clauseIndex literalIndex).tail.head? =
        some exit := by
  simpa
    [drawingFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes,
      drawingFixedEightPositionedPeriodicPlanarOneInThreeRawFormula,
      drawingFixedEightPeriodicPlanarOneInThreeRawPlacement] using
    PeriodicOneInThreePositioned.splicedRoutes_exists_tail_head?_of_members
      (drawingAngularEightOccurrenceSplitPositionedFormula input)
      (drawingAngularEightOccurrenceSplitPlacement input)
      (drawingAngularEightOccurrenceSplitPositionedFormula_widthAtMostThree
        input sourceWidth)
      (drawingAngularEightOccurrenceSplitPositionedFormula_allAtomsNodup
        input sourceLocal sourceWidth sourceOccurrences)
      (drawingFixedEightPeriodicPlanarOneInThreeInheritedRouteSuffixes
        input sourceLocal sourceWidth sourceOccurrences)
      clauseMember literalMember

end PeriodicOrthocrossing
end LeanTrominoes
