import LeanTrominoes.PeriodicCNFPlanarFixedEightOneInThreeRoutes
import LeanTrominoes.PositionedPeriodicCNFCanonicalRouteRenaming

/-!
# Fixed-eight Figure 9 routes through opaque wrapping

The logical pipeline wraps every raw Figure 9 variable in an opaque
one-field type before unit elimination.  The wrapper changes neither
coordinates nor periodic offsets, so the complete raw route family is reused
verbatim.  Canonical endpoint and orthogonality certificates transfer
through the generic renaming theorem.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- The complete raw Figure 9 route family, reused after opaque variable
wrapping. -/
noncomputable def
    drawingFixedEightPeriodicPlanarOneInThreeIncidenceRoutes
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable)
    (sourceLocal : input.IsLocal)
    (sourceWidth : input.WidthAtMost 3)
    (sourceOccurrences : input.OccurrencesAtMost 3) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  drawingFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes
    input sourceLocal sourceWidth sourceOccurrences

/-- Every wrapped fixed-eight Figure 9 route retains exact canonical
endpoints and orthogonality. -/
theorem
    drawingFixedEightPeriodicPlanarOneInThreeIncidenceRoutes_valid
    {Variable : Type*} [DecidableEq Variable]
    (input : PeriodicCNF Variable)
    (sourceLocal : input.IsLocal)
    (sourceWidth : input.WidthAtMost 3)
    (sourceOccurrences : input.OccurrencesAtMost 3)
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (drawingFixedEightPositionedPeriodicPlanarOneInThreeFormula
          input).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (WrappedPeriodicVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    (drawingFixedEightPeriodicPlanarOneInThreeIncidenceRoutes
        input sourceLocal sourceWidth sourceOccurrences
        clauseIndex literalIndex).head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            (drawingFixedEightPeriodicPlanarOneInThreePlacement input)
            clause) ∧
      (drawingFixedEightPeriodicPlanarOneInThreeIncidenceRoutes
        input sourceLocal sourceWidth sourceOccurrences
        clauseIndex literalIndex).getLast? =
        some
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (drawingFixedEightPeriodicPlanarOneInThreePlacement input)
            clause literal) ∧
      PeriodicOrthocrossing.OrthogonalPolyline
        (drawingFixedEightPeriodicPlanarOneInThreeIncidenceRoutes
          input sourceLocal sourceWidth sourceOccurrences
          clauseIndex literalIndex) := by
  let rawFormula :=
    drawingFixedEightPositionedPeriodicPlanarOneInThreeRawFormula input
  let rawPlacement :=
    drawingFixedEightPeriodicPlanarOneInThreeRawPlacement input
  let wrappedPlacement :=
    drawingFixedEightPeriodicPlanarOneInThreePlacement input
  let routes :=
    drawingFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes
      input sourceLocal sourceWidth sourceOccurrences
  have rawEndpoints :
      ∀ sourceClause sourceClauseIndex,
        (sourceClause, sourceClauseIndex) ∈ rawFormula.clauses.zipIdx →
        ∀ sourceLiteral sourceLiteralIndex,
          (sourceLiteral, sourceLiteralIndex) ∈
              sourceClause.literals.zipIdx →
          (routes sourceClauseIndex sourceLiteralIndex).head? =
              some
                (PositionedPeriodicCNF.canonicalClausePosition
                  rawPlacement sourceClause) ∧
            (routes sourceClauseIndex sourceLiteralIndex).getLast? =
              some
                (PositionedPeriodicCNF.canonicalLiteralPosition
                  rawPlacement sourceClause sourceLiteral) := by
    intro sourceClause sourceClauseIndex sourceClauseMember
      sourceLiteral sourceLiteralIndex sourceLiteralMember
    have valid :=
      drawingFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes_valid
        input sourceLocal sourceWidth sourceOccurrences
        sourceClauseMember sourceLiteralMember
    exact ⟨valid.1, valid.2.1⟩
  have rawOrthogonal :
      ∀ sourceClause sourceClauseIndex,
        (sourceClause, sourceClauseIndex) ∈ rawFormula.clauses.zipIdx →
        ∀ sourceLiteral sourceLiteralIndex,
          (sourceLiteral, sourceLiteralIndex) ∈
              sourceClause.literals.zipIdx →
          PeriodicOrthocrossing.OrthogonalPolyline
            (routes sourceClauseIndex sourceLiteralIndex) := by
    intro sourceClause sourceClauseIndex sourceClauseMember
      sourceLiteral sourceLiteralIndex sourceLiteralMember
    exact
      (drawingFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes_valid
        input sourceLocal sourceWidth sourceOccurrences
        sourceClauseMember sourceLiteralMember).2.2
  have endpoints :=
    PositionedPeriodicCNF.canonicalIncidenceRoutes_endpoints_rename
      rawFormula rawPlacement wrappedPlacement routes
      WrappedPeriodicVariable.mk rawEndpoints
      (fun _ => rfl) rfl clauseMember literalMember
  have orthogonal :=
    PositionedPeriodicCNF.canonicalIncidenceRoutes_orthogonal_rename
      rawFormula routes WrappedPeriodicVariable.mk rawOrthogonal
      clauseMember literalMember
  simpa [drawingFixedEightPeriodicPlanarOneInThreeIncidenceRoutes,
    rawFormula, rawPlacement, wrappedPlacement, routes,
    drawingFixedEightPositionedPeriodicPlanarOneInThreeFormula,
    drawingFixedEightPeriodicPlanarOneInThreePlacement] using
      ⟨endpoints.1, endpoints.2, orthogonal⟩

end PeriodicOrthocrossing
end LeanTrominoes
