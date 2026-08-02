import LeanTrominoes.PeriodicOneInThreePositionedInheritedRouteFamily
import LeanTrominoes.PeriodicOneInThreePositionedInheritedRouteIsolation

/-!
# Endpoint isolation for inherited Figure 9 suffix families

This module lifts the per-route Figure 9 connector calculation through the
proof-backed inherited-incidence selector.  Thus any nondegenerate simple
orthogonal source route family gives inherited Figure 9 suffixes whose final
endpoints remain isolated after unit subdivision.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreePositioned

/-- Pointwise source simplicity and nondegeneracy lift to final-endpoint
isolation of every genuine inherited Figure 9 suffix. -/
theorem inheritedRouteSuffixesRoutes_lastNotInDropLast
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    (sourceRoutes : PositionedPeriodicCNF.IncidenceRoutes)
    (sourceEndpoints :
      ∀ sourceClause sourceClauseIndex,
        (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx →
        ∀ sourceLiteral sourceLiteralIndex,
          (sourceLiteral, sourceLiteralIndex) ∈
              sourceClause.literals.zipIdx →
          (sourceRoutes sourceClauseIndex sourceLiteralIndex).head? =
              some
                (PositionedPeriodicCNF.canonicalClausePosition
                  sourcePlacement sourceClause) ∧
            (sourceRoutes sourceClauseIndex sourceLiteralIndex).getLast? =
              some
                (PositionedPeriodicCNF.canonicalLiteralPosition
                  sourcePlacement sourceClause sourceLiteral))
    (sourceOrthogonal :
      ∀ sourceClause sourceClauseIndex,
        (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx →
        ∀ sourceLiteral sourceLiteralIndex,
          (sourceLiteral, sourceLiteralIndex) ∈
              sourceClause.literals.zipIdx →
          PeriodicOrthocrossing.OrthogonalPolyline
            (sourceRoutes sourceClauseIndex sourceLiteralIndex))
    (sourceLength :
      ∀ sourceClause sourceClauseIndex,
        (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx →
        ∀ sourceLiteral sourceLiteralIndex,
          (sourceLiteral, sourceLiteralIndex) ∈
              sourceClause.literals.zipIdx →
          2 ≤ (sourceRoutes sourceClauseIndex sourceLiteralIndex).length)
    (sourceSimple :
      ∀ sourceClause sourceClauseIndex,
        (sourceClause, sourceClauseIndex) ∈ source.clauses.zipIdx →
        ∀ sourceLiteral sourceLiteralIndex,
          (sourceLiteral, sourceLiteralIndex) ∈
              sourceClause.literals.zipIdx →
          LocalIncidenceDrawing.RouteIsSimple
            (sourceRoutes sourceClauseIndex sourceLiteralIndex))
    {clause : PositionedPeriodicClause (OneInThreeVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ (formula source).clauses.zipIdx)
    {literal : PeriodicLiteral (OneInThreeVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (sourceAtom : Variable)
    (literalSource : literal.atom = .inl sourceAtom) :
    AxisDirection.LastNotInDropLast
      (AxisDirection.unitSubdividePolyline
        (inheritedRouteSuffixesRoutes
          source sourcePlacement sourceRoutes
          clauseIndex literalIndex)) := by
  rcases inheritedIncidenceData?_of_members
      source sourcePlacement sourceWidth sourceDistinct
      clauseMember literalMember sourceAtom literalSource with
    ⟨data, dataLookup⟩
  have endpoints :=
    sourceEndpoints
      data.sourceClause data.sourceClauseIndex
      data.sourceClauseMember
      data.sourceLiteral data.sourceLiteralIndex
      data.sourceLiteralMember
  have isolated :=
    inheritedRouteSuffix_lastNotInDropLast
      (placement source sourcePlacement)
      sourcePlacement data.sourceClause data.generatedClause
      data.sourceLiteralIndex
      (sourceRoutes data.sourceClauseIndex data.sourceLiteralIndex)
      endpoints.1 endpoints.2
      (sourceLength
        data.sourceClause data.sourceClauseIndex
        data.sourceClauseMember
        data.sourceLiteral data.sourceLiteralIndex
        data.sourceLiteralMember)
      (sourceOrthogonal
        data.sourceClause data.sourceClauseIndex
        data.sourceClauseMember
        data.sourceLiteral data.sourceLiteralIndex
        data.sourceLiteralMember)
      (sourceSimple
        data.sourceClause data.sourceClauseIndex
        data.sourceClauseMember
        data.sourceLiteral data.sourceLiteralIndex
        data.sourceLiteralMember)
  simpa [inheritedRouteSuffixesRoutes, dataLookup] using isolated

end PeriodicOneInThreePositioned
end LeanTrominoes
