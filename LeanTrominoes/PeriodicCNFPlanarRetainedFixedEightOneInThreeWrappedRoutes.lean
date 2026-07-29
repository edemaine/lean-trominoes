import LeanTrominoes.PeriodicCNFPlanarRetainedFixedEightOneInThreeRoutes
import LeanTrominoes.PositionedPeriodicCNFCanonicalRouteRenaming

/-!
# Retained Figure 9 routes through opaque wrapping

The exact-one wrapper changes neither coordinates nor periodic offsets, so
the retained raw Figure 9 routes can be reused verbatim.  Generic canonical
route renaming transports their endpoint, orthogonality, and first-exit
certificates.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- The retained raw Figure 9 route family, reused after opaque wrapping. -/
noncomputable def
    retainedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  retainedFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes
    source sourceLocal sourceWidth sourceOccurrences
    sourceClausesNonempty

/-- Every wrapped retained Figure 9 route keeps its canonical endpoints and
orthogonality. -/
theorem
    retainedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes_valid
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedFixedEightPositionedPeriodicPlanarOneInThreeFormula
          source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (WrappedPeriodicVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    (retainedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseIndex literalIndex).head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            (retainedFixedEightPeriodicPlanarOneInThreePlacement source)
            clause) ∧
      (retainedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseIndex literalIndex).getLast? =
        some
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (retainedFixedEightPeriodicPlanarOneInThreePlacement source)
            clause literal) ∧
      PeriodicOrthocrossing.OrthogonalPolyline
        (retainedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty clauseIndex literalIndex) := by
  let rawFormula :=
    retainedFixedEightPositionedPeriodicPlanarOneInThreeRawFormula source
  let rawPlacement :=
    retainedFixedEightPeriodicPlanarOneInThreeRawPlacement source
  let wrappedPlacement :=
    retainedFixedEightPeriodicPlanarOneInThreePlacement source
  let routes :=
    retainedFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
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
      retainedFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes_valid
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty sourceClauseMember sourceLiteralMember
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
      (retainedFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes_valid
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty sourceClauseMember sourceLiteralMember).2.2
  have endpoints :=
    PositionedPeriodicCNF.canonicalIncidenceRoutes_endpoints_rename
      rawFormula rawPlacement wrappedPlacement routes
      WrappedPeriodicVariable.mk rawEndpoints
      (fun _ => rfl) rfl clauseMember literalMember
  have orthogonal :=
    PositionedPeriodicCNF.canonicalIncidenceRoutes_orthogonal_rename
      rawFormula routes WrappedPeriodicVariable.mk rawOrthogonal
      clauseMember literalMember
  simpa [retainedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes,
    rawFormula, rawPlacement, wrappedPlacement, routes,
    retainedFixedEightPositionedPeriodicPlanarOneInThreeFormula,
    retainedFixedEightPeriodicPlanarOneInThreePlacement] using
      ⟨endpoints.1, endpoints.2, orthogonal⟩

/-- Opaque wrapping also preserves every retained Figure 9 route's first
exit. -/
theorem
    retainedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes_exists_tail_head?
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedFixedEightPositionedPeriodicPlanarOneInThreeFormula
          source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (WrappedPeriodicVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    ∃ exit,
      (retainedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseIndex literalIndex).tail.head? =
        some exit := by
  let rawFormula :=
    retainedFixedEightPositionedPeriodicPlanarOneInThreeRawFormula source
  let routes :=
    retainedFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  have transferred :=
    PositionedPeriodicCNF.incidenceIndexProperty_rename
      rawFormula WrappedPeriodicVariable.mk
      (fun sourceClauseIndex sourceLiteralIndex =>
        ∃ exit,
          (routes sourceClauseIndex sourceLiteralIndex).tail.head? =
            some exit)
      (fun _sourceClause _sourceClauseIndex sourceClauseMember
          _sourceLiteral _sourceLiteralIndex sourceLiteralMember =>
        retainedFixedEightPeriodicPlanarOneInThreeRawIncidenceRoutes_exists_tail_head?
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty sourceClauseMember sourceLiteralMember)
      clauseMember literalMember
  simpa
    [retainedFixedEightPeriodicPlanarOneInThreeIncidenceRoutes,
      retainedFixedEightPositionedPeriodicPlanarOneInThreeFormula,
      rawFormula, routes] using transferred

end PeriodicOrthocrossing
end LeanTrominoes
